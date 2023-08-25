####  Due 2023 Aug 25 (Today)
- translate to custom CHC intermediate language (60%)
    - denotation of subtyping into horn clauses 
    - use three kinds of identifiers: 
        - learnable predicates/types
        - constraint predicates/types
        - inhabitants of predicates/types
    - divide translation into three sections: 
        - abstract translation: generate rules for abstract reasoning
        - refined translation: generate rules for refined reasoning
        - simplification: remove extraneous information
    - the horn-clause translation normalizes subtyping by removing quantifiers (univ, exis, induc, coinduc)
    - the quantification is inferred by context: 
        - learnable variable on RHS means least solution (union until valid)
        - learnable variable on LHS means greatest solution (intersect until valid)
    - restrict second order bound variables to LHS of subtyping (weakening to FOL semantics)

#### Due 2023 Sep 01 (Next) 
- determine feasibility of RInGen (the SOTA for solving inductive algebraic data types) 
    - look into RInGen tool for handling inductive ADTs (Kostyukov et al)
    - read *Beyond the Elementary Representations of Program Invariants over Algebraic Data Types*.
        - by Yurii Kostyukov, Dmitry Mordvinov & Grigory Fedyukovich 
        - 2021
        - regular vs elementary representations of constraints
            - regular: automata-based
            - elementary: first-order logic
        - supports relations
        - a tree automaton is a generalization of an algebraic data type 
            - tree automaton/ADT is used to represent sorts
                - defining the shapes of the predicate inhabitants / function arguments
            - it can have repeated constructors
            - e.g. 
                - `even ::= Z | S S even`  
                - `Z |-> q_even, S q_odd |-> q_even, S q_odd |-> q_even, ... |-> q_even`  
    - use custom CHC intermediate lang to guide construction of examples (e.g. foldn) in RInGen 
- determine novelty of relational types relative to ADT CHC SOTA
- translate to custom CHC intermediate language (100%)

#### Due 2023 Sep 08 
- either translate to RInGen
- or write a custom CHC solver with specialized logic for the type language
    - if the existing solvers are insufficient
    - simply avoid using termination heuristic to be more complete

#### Due 2023 Sep 15 
- translate to RInGen or write custom solver
- propose/encode benchmarks
- propose/encode meta-theorems 
- tidy up

#### Due 2023 Sep 22 
- evaluate benchmarks 
- prove meta-theorems

#### Due 2023 Sep 29
- evaluate benchmarks 
- prove meta-theorems

#### Due 2023 Oct 06
- evaluate benchmarks 
- prove meta-theorems

#### Due 2023 Oct 13
- write paper

#### Due 2023 Oct 20
- write paper

#### Due 2023 Oct 27
- write paper

#### Due 2023 Nov 03
- write paper (100%)