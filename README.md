## schedule
> Due 2023 Aug 25
- translate to custom CHC-type language
    - translation is the semantics of subtyping as denotation into horn clauses
    - start with idealized clauses of subtyping entailment
    - the horn-clause translation simplifies by removing quantifiers (univ, exis, induc, coinduc)
    - the (unions, existential, induction)/(intersections, universal, co-induction)
        - are inferred by context: 
            - rhs variable implies least solution (union until valid)
            - lhs variable implies greatest solution (intersect until valid)
    - in order to visualize the ideal CHC language for refined reasoning
    - convert co-induction to induction with implication to allow simplifying on lhs
- evaluate existing solvers for feasibility
    - Yurii Kostyukov, Dmitry Mordvinov & Grigory Fedyukovich (2021): Beyond the Elementary Representations of Program Invariants over Algebraic Data Types.
    - see if solvers have specialized logic for solving for arguments of horn clauses
    - understand if subtyping entailment needs to be abandoned in favor of typing entailment 
    - try running the CHC-type translation on foldn example
    - try to manually construct CHC problem for the foldn example
- translate to CHC solver language
    - turn types on lhs into horn clauses for learning predicates for identifiers
        - used for abstract reasoning phase
    - turn types on rhs types (specs) for decomposing constraints 
        - used for refined reasoning/interpolation phase
    - consider how implication should be transformed
- choose backend (Lean or some CHC solver); Lean seems too difficult
    - translating to Lean would require finding the top type and constructing refinement types
    - or avoiding datatypes completely and using sets of labeled things
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