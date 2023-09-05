## Relational Types

#### Hypothesis
- relational type inference is equivalent to CHC solving

#### Innovation
- An expressive type language with an alternative view of deducing and abducing types
- mirrors the structure of programs (a la liquid types)
- learns by unwinding (a la duality)
- easy to provide annotations and confine their locality 
- equivalent to horn clauses 
- subtyping solving instead of CHC (different, not better)  
    - allows annotations and specs to be written succinctly 
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
        - similar: relies on duality 
            - CHC: decide `A <: B` by refuting `A and not B` and learning interpolant 
                - duality constructs predicates by unwinding inductive constraints
                - this amounts to deriving disjunctions, right?
                - the interpolant is a learned upper bound on program term
                    - e.g. for `foo(t)`, `foo : A -> B`, `t : T`, 
                        the interpolant is `I` where `T <: I <: A`
            - subtyping: decide `A <: B` by decomposing types and choosing values for learnable type variables
    - comparison to bi-directional propagation
        - similar: relies on duality 
            - assuming program `a`, decide `a : B` by propagating `B` down `a`
    - comparison to SYNGAR  
        - if the program is spurious, then the negation of the IO example 
        - is propagated down the spurious program tree.
        - a separate notion of tree automata is used to generate candidate programs 
- tracks the distinction between 
    - type variables acting as constraints and 
    - those acting as learnable predicates
    - by marking parameter and return type variables  
- learning unions vs intersections is discriminated 
    - according to the side of the subtyping relation.
    - this should be consistent with craig interpolation criteria: 
        - the learned type contains only symbols in the intersection of the 
            subtree and the rest of the tree (type tree, that is)
        - need to verify this idea
    - learning unions is deductive; i.e. the grounding is certain (could become weaker)
    - learning intersections is abductive; i.e. the grounding is uncertain (could become stronger)

#### Limitations
- cannot ensure termination
    - because the search space is not bounded by a top data type


#### Future directions
- bidirectional propagation
- program synthesis
- data-driven

#### Results
- runtime semantics
- CHC semantics
- typing semantics
- subtyping semantics
- compilation into horn clauses
- type inference and unification algorithm 
- soundness proofs down to runtime semantics
- benchmarks showing verification/synthesis problems that can be solved
- comparison of 
    - custom unification algorithm vs
    - compilation to horn clause and running on CHC solver  


#### TODO
- reintegrate infer and unification for type language
- remove overly conservative divergence heuristic
- read Liquid Types and Synquid papers again
- read semantic subtyping paper
- read *Synthesizing Software Verifiers from Proof Rules*
- read *A Constraint-Based Approach to Solving Games on Infinite Graphs*
