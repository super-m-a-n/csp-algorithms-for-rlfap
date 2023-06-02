# RLFAP-csp-solver
## About
This project implements various constraint satisfaction problem algorithms. The algorithms are then used to solve the radio link frequency assignment problem (rlfap) and are compared on different input instances of the problem. The implementation is based on the Python code found in: https://github.com/aimacode/aima-python/blob/master/csp.py
## File structure
* In folder ```/data/``` : Input instances of the rlfa problem. Files with prefix ```var``` define the instance's variables,  with prefix ```dom``` define the domains of the variables of the instance and prefix ```ctr``` define the constraints of the instance.
* ```/src/main-rlfa.py``` : The implementation of the algorithms and the main functionality.
## RLFA problem definition
We are given a finite set of radio links (variables), a finite set of frequencies for each radio link (variable domains) and binary non linear constraints of the form ```|x_i-y_i| > k_i ```, where ```x_i, y_i``` are radio links - variables and ```k_i``` is a positive number. The problem wants to assign a frequency (positive number) to each of the radio link variables, so that all constraints are satisfied. More details about the problem can be found here: https://miat.inrae.fr/schiex/rlfap.shtml. Our algorithms focus on the satisfiability-version of the problem and not the the optimization version (both NP-hard).
## Algorithms implemented
* Forward Checking (FC)
* MAC (maintain arc consistency)
* Forward Checking with back jumping (FC-CBJ)
* Min Conflicts (local search / stochastic hill climbing type of algorithm)

We also use dynamic variable ordering, by implementing the dom/wdeg heuristic: http://www.frontiersinai.com/ecai/ecai2004/ecai04/pdf/p0146.pdf. \
For value assignment on the variables we use the least constraining value heuristic (lcv).
## Execution
```$ python src/main-rlfa.py <method>``` \
Where method is 1 for FC, 2 for MAC, 3 for FC-CBJ, 4 for Min-Conflicts.
