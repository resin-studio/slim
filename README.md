## Relational Types

#### Hypothesis
- subtyping constraints over relational types that mirror structure of programs are easier to solve than semantically equivalent horn clauses via CHC.

#### Innovation
- A expressive type language that 
1. mirrors the structure of programs 
2. easy to provide annotations and confine their locality 
3. as expressive as horn clauses
4. leveraging type's mirrored structure for easier problems to solve?  
    - type structure is derived from program structure
    - therefore, subtyping rules leverage program structure 
    - better than horn solvers as program structure dictates 
        - the optimal constraint to solve/check
    - how does liquid types leverage this structure?
        - it has a simple way of type checking the base type without using solver
    - downward propagation can leverage mirrored structure of type
5. tracks the distinction between 
    - type variables acting as constraints and 
    - those acting as learnable predicates
    - by marking parameter and return type variables  
6. learning unions vs intersections is discriminated 
    - according to the side of the subtyping relation.
7. equivalent to horn clauses 

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
