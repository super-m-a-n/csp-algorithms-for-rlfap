"""We read the var,dom,ctr files here and call the RLFA problem using csp algorithms and heuristics"""

import argparse
import sys
import string
import csp
import search
import utils
import time
import numpy

from csp import dom_j_up
from csp import num_legal_values
from csp import lcv

# enhanced variable ordering heuristics (from paper)
def dom_wdeg(assignment, csp):
    """Minimum ratio of (domain size / weighted degree) heuristic"""
    def key_function(var):      # this function calculates the (domain size / weighted degree) ratio for var
        wdeg = csp.weighted_degree(var, assignment)
        if (wdeg != 0):
            return num_legal_values(csp, var, assignment) / wdeg
        else:
            return float('inf')
    return argmin([v for v in csp.variables if v not in assignment], key_function)      # return variable with smallest such ratio
    #return utils.argmin_random_tie([v for v in csp.variables if v not in assignment], key_function)

def argmin(seq, key_function):
    """Return a minimum element of seq, based on key_function value"""
    return min(seq, key=key_function)

class rlfaCSP(csp.CSP):
    """The class definition of the rlfa csp problem, as a subclass of superclass CSP"""

    def __init__(self, variables, domains, neighbors, constraints):
        """initializes rlfa CSP instance with variables, domains, neighbors, constraints"""
        csp.CSP.__init__(self, variables, domains, neighbors, self.rlfa_constraints)     #call superclass constructor
        self.ctr_dict = constraints
        self.weights = {}       # a dictionary with the binary constraints (2-tuples) of rlfa as keys, and the weight of each constraint as value, needed for dom/wdeg heuristic
        for ctr in self.ctr_dict:
            self.weights[ctr] = 1               # to begin with, all weights are initialized to 1
        self.conflict_sets = {}                 # a dictionary with variables of csp as keys and the conflict sets of each variable as values
        for var in self.variables:              #elements of conflict set are tuples : (variable, depth of variable in assignment)
            self.conflict_sets[var] = set()
        self.checks = 0                         #variable to keep track of the number of constraint checks during each algorithm

    def rlfa_constraints(self, V1, val1, V2, val2):
        """constraints function for rlfa csp"""
        if (V1,V2) in self.ctr_dict:            #it is enough to check arc (V1,V2), since if val1,val2 satisfies the constraint (V1,V2) it will satisfy the constraint (V2,V1)
            ctr = self.ctr_dict[(V1,V2)]        #access constraints dictionary
            operator = ctr[0]
            k = ctr[1]
            if operator == '=':     #check if constraint holds, based on operator of constraint
                return (abs(val1 - val2) == k)
            elif operator == '>':
                return (abs(val1 - val2) > k)
        return True     #there is no arc (V1,V2) (hence no (V2,V1)) in constraints dictionary, so there are no constraints to be checked, all constraints are satisfied

    def solve(self, method):
        global begin
        begin = time.time()
        if method == 1:
            result = backtracking_search(self, dom_wdeg, csp.lcv, mac)
        elif method == 2:
            result = backtracking_search(self, dom_wdeg, csp.lcv, forward_checking)
        elif method == 3:
            result = fc_cbj_backjumping(self, dom_wdeg, csp.lcv, forward_checking_cbj)
        elif method == 4:
            result = min_conflicts(self, 10000)
            if result[0] != None:
                print("Problem found SAT within 10000 iterations of min-conflicts")
            else:
                print("Either problem is UNSAT or no solution was found within 10000 iterations")
                print("Number of violated constraints after 10000 iterations : ", result[1])
            print("\n\n")
            return

        end = time.time()
        if result == -1:      #threshold of 150s exceeded
            print("Exceeded threshold of 150s without founding solution, in total time : " + str(end - begin))
            print("Number of assignments / visited nodes : > ", self.nassigns)
            print("Number of constraint checks : > ", self.checks)
        elif result is None:
            print("Problem found UNSAT in total time : " + str(end - begin))
            print("Number of assignments / visited nodes : ", self.nassigns)
            print("Number of constraint checks : ", self.checks)
        else:
            print("Problem found SAT in total time : " + str(end - begin))
            print("Number of assignments / visited nodes : ", self.nassigns)
            print("Number of constraint checks : ", self.checks)
        print("\n\n")

    def weighted_degree(self, var, assignment):
        """Returns the sum of the weights of the constraints of csp,
        where the constraint is between var and another uninstantiated variable (not in assignment)
        This function is csp-specific, that is why we put it inside rlfap class"""
        sum = 0
        unassigned_vars = [v for v in self.neighbors[var] if v not in assignment]
        for v in unassigned_vars:
                sum += self.weights[(var, v)]
        return sum

def forward_checking(csp, var, value, assignment, removals):
    """Prune neighbor values inconsistent with var=value."""
    """Increments weights of responsible constraints, when a domain wipeout happens, so that it supports the dom/wdeg heuristic"""
    csp.support_pruning()
    for B in csp.neighbors[var]:
        if B not in assignment:
            for b in csp.curr_domains[B][:]:
                if not csp.constraints(var, value, B, b):
                    csp.prune(B, b, removals)
                csp.checks += 1
            if not csp.curr_domains[B]:     # domain wipeout occured, increment weight counters of responsible constraints
                csp.weights[(B,var)] += 1
                csp.weights[(var,B)] += 1
                return False
    return True

def AC3(csp, queue=None, removals=None, arc_heuristic=dom_j_up):
    """[Figure 6.3]"""
    """Calls the new revise function that supports the dom/wdeg heuristic"""
    if queue is None:
        queue = {(Xi, Xk) for Xi in csp.variables for Xk in csp.neighbors[Xi]}
    csp.support_pruning()
    queue = arc_heuristic(csp, queue)
    checks = 0
    while queue:
        (Xi, Xj) = queue.pop()
        revised, checks = revise(csp, Xi, Xj, removals, checks)
        if revised:
            if not csp.curr_domains[Xi]:
                csp.checks += checks
                return False, checks  # CSP is inconsistent
            for Xk in csp.neighbors[Xi]:
                if Xk != Xj:
                    queue.add((Xk, Xi))
    csp.checks += checks
    return True, checks  # CSP is arc consistent

def revise(csp, Xi, Xj, removals, checks=0):
    """Return true if we remove a value."""
    """A check for domain wipeout is inserted at the end to support the dom/wdeg heuristic"""
    """In case of a domain wipeout, the weights of the responsible constraints are incremented"""
    revised = False
    for x in csp.curr_domains[Xi][:]:
        # If Xi=x conflicts with Xj=y for every possible y, eliminate Xi=x
        # if all(not csp.constraints(Xi, x, Xj, y) for y in csp.curr_domains[Xj]):
        conflict = True
        for y in csp.curr_domains[Xj]:
            if csp.constraints(Xi, x, Xj, y):
                conflict = False
            checks += 1
            if not conflict:
                break
        if conflict:
            csp.prune(Xi, x, removals)
            revised = True
    if not csp.curr_domains[Xi]:        #domain wipeout, increment responsible constraints's weights counters
        csp.weights[(Xi,Xj)] += 1
        csp.weights[(Xj,Xi)] += 1
    return revised, checks

def mac(csp, var, value, assignment, removals, constraint_propagation=AC3):
    """Maintain arc consistency."""
    """Calls the new AC3 constraint propagation that supports the dom/wdeg heuristic"""
    return constraint_propagation(csp, {(X, var) for X in csp.neighbors[var]}, removals)

def backtracking_search(csp, select_unassigned_variable, order_domain_values, inference):
    """[Figure 6.5]"""
    """Added time threshold of 2.5 minutes (150s)"""
    def backtrack(assignment):
        if len(assignment) == len(csp.variables):
            return assignment
        if (time.time() - begin) > 150:     #if you exceed time threshold of 150s, return -1, which means problem was cutoff
            return -1
        var = select_unassigned_variable(assignment, csp)
        for value in order_domain_values(var, assignment, csp):
            if 0 == csp.nconflicts(var, value, assignment):
                csp.assign(var, value, assignment)
                removals = csp.suppose(var, value)
                if inference(csp, var, value, assignment, removals):
                    result = backtrack(assignment)
                    if result is not None:
                        return result
                csp.restore(removals)
        csp.unassign(var, assignment)
        return None

    result = backtrack({})
    if result != -1:
        assert result is None or csp.goal_test(result)
    return result


def fc_cbj_backjumping(csp, select_unassigned_variable, order_domain_values, inference):
    """Added time threshold of 2.5 minutes (150s)"""
    """Implements fc_cbj_backjumping algorithm"""
    """result is a tuple now (solution,jump), where solution is a complete assignment or None if no such assignment was found"""
    """jump is a variable to backjump to, or None, if no variable to backjump to was found"""
    def fc_cbj(assignment):
        if len(assignment) == len(csp.variables):
            return (assignment, None)
        if (time.time() - begin) > 150:     #if you exceed time threshold of 150s, return (-1, None), which means problem was cutoff and no solution was found
            return (-1, None)
        var = select_unassigned_variable(assignment, csp)
        for value in order_domain_values(var, assignment, csp):
            if 0 == csp.nconflicts(var, value, assignment):
                csp.assign(var, value, assignment)
                removals = csp.suppose(var, value)
                if inference(csp, var, value, assignment, removals):
                    result = fc_cbj(assignment)
                    if result[0] is not None:       #if a solution to csp is found or threshold is exceeded
                        return result           #return the solution or just return empty handed
                    elif result[1] is not None:    #if no solution to csp was found, but a variable to backjump to was returned
                        if result[1] != var:       #if current variable var is not backjump's destination variable
                            csp.unassign(var, assignment)       # unassign current variable value from assignment (we are backjumping)
                            csp.restore(removals)               # restore any changes to domains caused by assignment to current variable (we are backjumping)
                            for variable in csp.conflict_sets:
                                (csp.conflict_sets[variable]).discard((var,len(assignment) + 1))        # restore conflict sets
                            return result       #return result, until you reach backjump's destination variable
                    else:  #problem is unsat
                        return result
                csp.restore(removals)
        csp.unassign(var, assignment)
        #reaching this point of execution, means all possible values of var failed, so we backjump to last variable of conflict set of var
        if not csp.conflict_sets[var]:     #conflict set of var is empty, and all possible values of var failed, return UNSAT
            return (None,None)
        jump_var = max(csp.conflict_sets[var], key=lambda t:t[1])      #backjump variable is deepest variable in conflict set of var
        csp.conflict_sets[jump_var[0]] = csp.conflict_sets[jump_var[0]].union(csp.conflict_sets[var]) - set([jump_var])  #update jump_var's conflict set with current var conflict set
        for variable in csp.conflict_sets:
            (csp.conflict_sets[variable]).discard((var,len(assignment) + 1))    #restore conflict sets
        return (None,jump_var[0])

    result = fc_cbj({})
    if result[0] != -1:
        assert result[0] is None or csp.goal_test(result[0])
    return result[0]

def forward_checking_cbj(csp, var, value, assignment, removals):
    """Prune neighbor values inconsistent with var=value."""
    """Increments weights of responsible constraints, when a domain wipeout happens, so that it supports the dom/wdeg heuristic"""
    """Updates conflict sets of neighbors of var appropriately, adds var to neighbor's conflict set, if we prune a value from neighbor"""
    csp.support_pruning()
    for B in csp.neighbors[var]:
        if B not in assignment:
            pruned = False
            for b in csp.curr_domains[B][:]:
                if not csp.constraints(var, value, B, b):
                    csp.prune(B, b, removals)
                    pruned = True
                csp.checks += 1
            if pruned == True:      # if var caused a value of domain of B to get pruned, add var into conflict set of B
                depth = len(assignment)
                (csp.conflict_sets[B]).add((var,depth))
            if not csp.curr_domains[B]:     # domain wipeout, increment weight counters of responsible constraints
                csp.weights[(B,var)] += 1
                csp.weights[(var,B)] += 1
                csp.conflict_sets[var] = csp.conflict_sets[var].union(csp.conflict_sets[B]) - set([(var,depth)])  #  B domain got wiped out, add conf set of B to conf set of var
                return False
    return True


def min_conflicts(csp, max_steps=100000):
    """Solve a CSP by stochastic Hill Climbing on the number of conflicts."""
    """Returns a tuple (solution, number of conflicts-constraint violations)"""
    """So if it finds solution returns (solution,0), otherwise returns (None, #violated_constraints)"""
    # Generate a complete assignment for all variables (probably with conflicts)
    csp.current = current = {}
    for var in csp.variables:
        val = min_conflicts_value(csp, var, current)
        csp.assign(var, val, current)
    # Now repeatedly choose a random conflicted variable and change it
    for i in range(max_steps):
        conflicted = csp.conflicted_vars(current)
        if not conflicted:
            return (current , 0)
        var = utils.random.choice(conflicted)
        val = min_conflicts_value(csp, var, current)
        csp.assign(var, val, current)
    # if min_conficts found no solution in max_steps, find how close we are to solution
    # count how many constraints are violated
    violated_constraints = 0
    for var in csp.variables:
        violated_constraints += csp.nconflicts(var, current[var], current)
    return (None, violated_constraints)


def min_conflicts_value(csp, var, current):
    """Return the value that will give var the least number of conflicts.
    If there is a tie, choose at random."""
    return utils.argmin_random_tie(csp.domains[var], key=lambda val: csp.nconflicts(var, val, current))





#___________________________________________________________________________________________________________________________

#main
parser = argparse.ArgumentParser()
parser.add_argument("method",
    help="Select csp method solver, Options: 1 : mac + dom/wdeg, 2 : fc + dom/wdeg, 3 : fc-cbj + dom/wdeg, 4 : min-conflicts",
    type=int)
args = parser.parse_args()
if args.method < 1 or args.method > 4:
    sys.exit("Invalid method number\n")

method = args.method

if method == 1:
    print("\nUsing MAC + dom/wdeg + lcv\n\n")
elif method == 2:
    print("\nUsing FC + dom/wdeg + lcv\n\n")
elif method == 3:
    print("\nUsing FC-CBJ + dom/wdeg + lcv\n\n")
elif method == 4:
    print("\nUsing min-conflicts local search\n\n")

#file reading

var_filenames = []  # list of names of var files (contains variables of csp)
dom_filenames = []  # list of names of dom files (contains domains of variables of csp)
ctr_filenames = []  # list of names of ctr files (contains constraints of csp)

#append the .txt file names of var,dom,ctr files

var_filenames.append("data/var2-f24.txt")
var_filenames.append("data/var2-f25.txt")
var_filenames.append("data/var3-f10.txt")
var_filenames.append("data/var3-f11.txt")
var_filenames.append("data/var6-w2.txt")
var_filenames.append("data/var7-w1-f4.txt")
var_filenames.append("data/var7-w1-f5.txt")
var_filenames.append("data/var8-f10.txt")
var_filenames.append("data/var8-f11.txt")
var_filenames.append("data/var11.txt")
var_filenames.append("data/var14-f27.txt")
var_filenames.append("data/var14-f28.txt")

dom_filenames.append("data/dom2-f24.txt")
dom_filenames.append("data/dom2-f25.txt")
dom_filenames.append("data/dom3-f10.txt")
dom_filenames.append("data/dom3-f11.txt")
dom_filenames.append("data/dom6-w2.txt")
dom_filenames.append("data/dom7-w1-f4.txt")
dom_filenames.append("data/dom7-w1-f5.txt")
dom_filenames.append("data/dom8-f10.txt")
dom_filenames.append("data/dom8-f11.txt")
dom_filenames.append("data/dom11.txt")
dom_filenames.append("data/dom14-f27.txt")
dom_filenames.append("data/dom14-f28.txt")

ctr_filenames.append("data/ctr2-f24.txt")
ctr_filenames.append("data/ctr2-f25.txt")
ctr_filenames.append("data/ctr3-f10.txt")
ctr_filenames.append("data/ctr3-f11.txt")
ctr_filenames.append("data/ctr6-w2.txt")
ctr_filenames.append("data/ctr7-w1-f4.txt")
ctr_filenames.append("data/ctr7-w1-f5.txt")
ctr_filenames.append("data/ctr8-f10.txt")
ctr_filenames.append("data/ctr8-f11.txt")
ctr_filenames.append("data/ctr11.txt")
ctr_filenames.append("data/ctr14-f27.txt")
ctr_filenames.append("data/ctr14-f28.txt")

#code section to open and read txt files

for i in range(len(dom_filenames)):
#for i in range(1,2):
    variables = []      # list of variables in our csp
    domains = {}        # a dictionary with variables of csp as keys and a list of values of domain for each variable as values
    neighbors = {}      # a dictionary with variables of csp as keys and a list of all variables-neighbors of a variable, for each variable in the csp graph, as values
    constraints = {}    # a dictionary with a 2-tuple of variables (V1,V2) as key, and the constraint, a 2-tuple (operator, k), as value, where operator : '=','>','<'
    doms = {}           #intermediate dictionary between domains and variables dictionary, has the domain id as key, a list of all the possible values in domain as values

    with open(dom_filenames[i], 'r') as dom_file:
        #this block processes the file, operator 'with' takes care of closing file, outside of block
        #extracts domains of variables of csp
        first_line = True
        for line in dom_file:
            if first_line:
                line = str(line)
                num_of_doms = int(line)
                first_line = False
                continue
            line = str(line)
            tokens = line.split(' ')
            dom_id = int(tokens[0])
            doms[dom_id] = [int(val) for val in tokens[2:]]

    with open(var_filenames[i], 'r') as var_file:
        #extracts variables of csp
        first_line = True
        for line in var_file:
            if first_line:
                line = str(line)
                num_of_vars = int(line)
                first_line = False
                continue
            line = str(line)
            tokens = line.split(' ')
            var_id = int(tokens[0])
            dom_id = int(tokens[1])
            variables.append(var_id)        #insert variable in variables list
            domains[var_id] = doms[dom_id]  #insert variable as key, variables domain values as values in domains dictionary

    with open(ctr_filenames[i], 'r') as ctr_file:
        #extracts the constraints of csp
        first_line = True
        for line in ctr_file:
            if first_line:
                line = str(line)
                num_of_ctrs = int(line)
                for var_id in variables:
                    neighbors[var_id] = []
                first_line = False
                continue
            line = str(line)
            tokens = line.split(' ')
            var_id1 = int(tokens[0])
            var_id2 = int(tokens[1])
            operator = tokens[2]
            k = int(tokens[3])
            neighbors[var_id1].append(var_id2)  #add var_id2 to the neighbors of var_id1
            neighbors[var_id2].append(var_id1)  #add var_id1 to the neighbors of var_id2
            constraints[(var_id1,var_id2)] = (operator, k)
            constraints[(var_id2,var_id1)] = (operator, k)

    #code section for solution of csp in different ways
    rlfa_csp = rlfaCSP(variables, domains, neighbors, constraints)      #initialize csp problem
    print("Finding results for file:" + dom_filenames[i][3:])
    rlfa_csp.solve(method)        #solve problem and display results
#___________________________________________________________________________________________________________________
