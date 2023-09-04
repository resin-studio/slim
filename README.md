## Relational Types

#### Hypothesis
- subtyping constraints over relational types that mirror structure of programs are easier to solve than semantically equivalent horn clauses via CHC.

#### Innovation
0. An expressive type language
1. mirrors the structure of programs (a la liquid types)
2. learns by unwinding (a la duality in CHC)
2. easy to provide annotations and confine their locality 
3. as expressive as horn clauses
4. leveraging type's mirrored structure for easier problems to solve?  
    - type structure is derived from program structure
    - therefore, subtyping rules leverage program structure 
    - better than horn solvers as program structure dictates 
        - the optimal constraint to solve/check
    - comparison to liquid types
        - similar: types mirror structure of program
            - it has a syntactic way of type checking the base type
            - by using qualified types?
        - Are these generated subtyping constraints really that different from horn clauses?
            - maybe because they are embedded in the datatype qualifier?
            - embedding the qualifier captures the derivation structure
            - thereby ensuring the optimal refinement search path?
        - different: relies on predicate abstraction (restricted to set of predicates)
            - instead of duality
            - predicate abstraction relies on conjunctions from predefined set of predicates  
    - comparison to solving CHC with duality
        - different: solving by searching for derivation in horn clauses
            - verify that CHC can't reuse the initial derivation.
            - the derivation has to make arbitrary choices on wether to unwind or not.
            - whereas, subtyping constraints unwind according to the structure, right?
        - similar: relies on duality 
            - duality constructs predicates by unwinding inductive constraints
            - this amounts to deriving disjunctions, right?
    - downward propagation can leverage mirrored structure of type
5. tracks the distinction between 
    - type variables acting as constraints and 
    - those acting as learnable predicates
    - by marking parameter and return type variables  
6. learning unions vs intersections is discriminated 
    - according to the side of the subtyping relation.
    - this should be consistent with craig interpolation criteria: 
        - the learned type contains only symbols in the intersection of the 
            subtree and the rest of the tree (type tree, that is)
        - need to verify this idea
    - learning unions is deductive; i.e. the grounding is certain (could become weaker)
    - learning intersections is abductive; i.e. the grounding is uncertain (could become stronger)
7. equivalent to horn clauses 
8. types have the advantage of leveraging existing proof structure  
    - CHC solving: prove `A <: B` by refuting `A and not B` 
        - must find single proof for `A` and `B`
    - bottom-up propagation: assuming proof `a : A`, decide `A <: B` by decomposing types
    according to a structure that mirrors the proof `a`.
    propagating `B` down `a`
    - top-down propagation: assuming program `a`, decide `a : B` by propagating `B` down `a`
        - related to SYNGAR
            - if the program is spurious, then the negation of the IO example 
            - is propagated down the spurious program tree.
            - a separate notion of tree automata is used to generate candidate programs 

#### Limitations
- cannot ensure termination
    - because the search space is not bounded by a top data type



#### Results
- benchmarks showing verification/synthesis problems that can be solved
- comparison of 
    - custom unification algorithm vs
    - compilation to horn clause and running on CHC solver  
- proof of soundness of relational type system


#### TODO
- reintegrate infer and unification for type language
- remove overly conservative divergence heuristic
- read Liquid Types and Synquid papers again
- read semantic subtyping paper
- read *Synthesizing Software Verifiers from Proof Rules*
- read *A Constraint-Based Approach to Solving Games on Infinite Graphs*
