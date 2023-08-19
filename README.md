## schedule
> Due 2023 Aug 25
- evaluate existing solvers for feasibility
    - see if solvers have specialized logic for solving for arguments of horn clauses
- translate to IR horn clause language
    - translate rhs types (specs) to placeholder constraint syntax
    - but turn types on lhs into horn clauses for learning predicates
- choose backend (Lean or some CHC solver)
- translation to predicate learning backend
- translate to rhs types (specs) to actual constraint language
    - constraint language is a specialized/refined logic solved via interpolation
- write a custom CHC solver with specialized logic for the type language
    - if the existing solvers are insufficient
    - could be similar to previous unification procedure 
    - simply avoid using termination heuristic to be more complete

> Due 2023 Sep 01 
- select benchmarks 
- complete first draft of backend translation (lean or CHC)

> Due 2023 Sep 08 
- evaluate 33% of benchmarks

> Due 2023 Sep 15 
- propose meta-theorems 

> Due 2023 Sep 22 
- evaluate 66% of benchmarks 
- prove 33% of meta-theorems

> Due 2023 Sep 29
- evaluate 100% of benchmarks 
- prove 66% of meta-theorems 

> Due 2023 Oct 06
- prove 100% of meta-theorems 

> Due 2023 Oct 13
- complete first draft of paper

> Due 2023 Oct 20
- complete second full draft of paper

> Due 2023 Oct 27
- complete third full draft of paper

> Due 2023 Nov 03
- complete final paper and all results