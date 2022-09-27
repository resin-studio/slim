/-

-- title --
type guided program synthesis for dynamically typed languages


-- criteria --
- correctness: strict and lenient
  - strict: reject programs with errors 
  - lenient: accept programs without errors 

- elaboration: unannotated types and incomplete terms 
  - unannotated types: infer types from terms
  - incomplete terms: synthesizes terms from types

- expressivity: types (specs) vs terms (programs) 
  - expressive programs: powerful features that can be combined with few restrictions
  - expressive types: granular decidable descriptions  

-- objective --
  - Slim Logic
    - strict: very good, not sound 
    - lenient: very good, incomplete
    - type inference: very good, nearly complete
    - term synthesis: good 
    - term expressivity: very good, 
      - in exchange of sound correctness
      - impredicative polymorphism, pattern matching, variants, records, open recursion  
    - type expressivity: very good
      - in exchange of type inference
      - impredicative types, relational inductive types, intersection types, union types, variant types, field types

-- benchmarks --
  - Standard ML
    - strict: best, sound 
    - lenient: decent, incomplete
    - type inference: very good, nearly complete
    - term synthesis: none
    - term expressivity: good 
      -- predicative polymorphism, pattern matching, variants, records, mutual recursion  
    - type expressivity: good 
      - predicative types, restricted induction types (datatypes), variant types (datatypes), record types 

  - Synquid 
    - strict: best, sound 
    - lenient: decent, incomplete
    - type inference: decent
    - term synthesis: good 
    - term expressivity: good 
      -- predicative polymorphism, pattern matching, variants, records, mutual recursion  
    - type expressivity: good 
      - predicative types, restricted induction types (datatypes), 
      - relational refinement types (liquid types)
      - variant types (datatypes), record types 

  - Pytype 
    - strict: decent, unsound 
    - lenient: good, incomplete
    - type inference: good 
    - term synthesis: none 
    - term expressivity: very good, 
      - in exchange of sound correctness
      - impredicative polymorphism, pattern matching, variants, records, open recursion  
    - type expressivity: good
      - impredicative types, record types, union types, variant types, field types



- Balance correctness and elaboration criteria:
  1. strict/unannotated **Standard ML**
    - reject erroneous programs with unannotated types
  2. strict/incomplete 
    - reject erroneous incomplete programs **Synquid**
    - remove erroneous programs from search space for synthesis
  3. lenient/unannotated 
    - accept error-free programs with unannotated types **Pytype**
  4. lenient/incomplete
    - accept error-free incomplete programs 
    - include interesting programs in search space for synthesis
- In exchange of soundness, offer automation for an expressive programming language
  - first-class functions
  - open recursion
  - variants, records
  - pattern matching
  - record projection
- In exchange of automation, offer soundness for an expressive annotation language
  - intersection types, union types
  - variant types, field types
  - inductive types
  - universal types, existential types 
  - type operations
  - boundend types
  - relational types

-- Concepts --

- kinds 
  - kinding serves two purposes: 
    - ensure wellformedness of types/typerators
    - ensure certain arity of types/typerators 
  - a kind categorizes a type or typerator by arity **Fω** - https://xavierleroy.org/CdF/2018-2019/2.pdf
  - keeping kinds syntactically distinct from types is useful for subtyping syntax in bounded quantification/typerator abstraction

- schemes 
  - predicativity is controlled by universes. **1ml** by Andreas Rossberg - https://people.mpi-sws.org/~rossberg/1ml/1ml.pdf

- relational types 
  - relate a type to parts of a relation **liquid types** 
    - liquid types uses boolean expressions to relate parts of types rather than subtypings
    - liquid types rely on SMT solvers check refinements
    - liquid types may have dependencies on values
  - relate a type to parts of a product type via product subtyping **novel** 
    - enforce that inductive subtype is decreasing pointwise to ensure termination e.g. `(.a #a A .b #b B) < (.a A .b B)`
    - obviate the need for outsourcing to SMT solver, 
    - allow reusing definitions for both checking and constructing subtypes 
    - avoid dependencies on values

- type equivalence
  - evaluate types to normalized forms

- consistent subtyping  
  - incorporates dynamic type
  - combine consistency with subtyping **gradual typing**
    - gradual typing supplements subtyping with masking or separate consistency relation
  - non-transitive dynamic subtyping **novel (maybe)** 
    - prevents everything from subtyping 
      e.g.
      X <: ?    ? <: T
      ------------------
            X <: T  

- constraint supertyping (type constraint strengthening)
  - propagate types in both directions for a given term **roundtrip typing**
  - collect and solve type constraints **hindley milner type system**
    - HM finds the least super type satisfying constraints
  - propagate types down and solve type constraints for all terms **novel** 
  - finds a somewhat lenient super type satsifying constraints **novel**
    - lenient to account for unforseen future constraints
  - constraint type inference:
    - produce a constraint C = ⟦Γ ⊢ t : τ⟧ that is both sufficient and necessary for C, Γ ⊢ t : τ to hold
    - can we relax the sufficient and necessary criteria? necessary but not sufficient (unsound)? 
  - what should be the relationship between type variables in Γ and type variables in C?
    - can Γ and C be merged by having constraints as a part of τ?
  - HM(X) presentation reuses term variables as scheme variables
  - modify HM(X) by creating a fresh type variable in let binding 
  - combine the declarative HM(X) (10-7) with constraint generation function (10-9)
    - maybe  Γ ⊢ t : τ :> τ ⊣ C
  - type solving can be combined with type equivalence
  - how does type computation relate to more general constraints?
  - should kind carry a constraint, rather than just a type?
  - constraints are turned inside out
  - there are no constraint combinators, only type combinators
  - there is only one constraint predicate: subtyping (≤)
  - combining constraints requires combining types and applying subtyping 
  - true ≅ _ ≤ ⊤
  - false ≅ _ ≤ ⊥
  - α₁ ≤ α₂ and β₁ ≤ β₂ ≅ α₁ ; β₁ ≤ α₂ ; β₂  
  - variable
    - decide constraint here instead of separate subsumption rule
    - constraint check also solves and unifies
        - e.g. Γ ; true ⊩ (∃ α ≤ ?, β ≤ ? . dict[α, β]) ≤ dict[str, ?] ~> α ≤ str, β ≤ ? 

    - might need to do renaming here to avoid collisions
    - or incorporate existential constraints
    - an existential constraint carries variables that should be renamed for broader contextfresh αᵢ # τ₁
      - however, we have separated the supertyping from the constraint

    using existential constraint type
    - Δ' contains tighter bounts on αᵢ
  - let binding
    - naming dynamic subparts is handles by recursive type inference
    - fresh names are inferred from inductive call for any unknown/dynamic parts of a type annotation
    - fresh names should be replaced by any known parts of type annotation  
    - fresh name constraints are simply included in generetated Γ'
      - e.g. Γ ⊢ {} : dict[str, ?] ≥ ∃ α ≤ ?, β ≤ ? . dict[α, β] ⊣ α ≤ str, β ≤ ? 
        - add solve/unify feature to constraint check

  existential constraint types serve three purposes:
  1. type inference: carries inferred constraints on types 
  2. relational specification: constrains subportions of types
  3. information hiding:

  - eager unification
  - using existential constraint type
  - function abstraction: fresh names are created for unknown/dynamic subparts of type annotation


-- unused concepts --

- refinement types
  - inference based on subtyping relation **ML refinement types**
    - ML refinement types of user-defined datatypes (variant types) are explicitly declared
      - datatype creates a named supertype (upper) bound. A
      - any type defined in terms of of the datatype's subtypes is defined as a datatype's subtype 
    - ML refinement types' intersections of user-defined types are inferred from subtyping relations
    - ML refinement types do not relate type to parts of a product type 

- collapsing types
  - various abstraction and composition portions of types and terms are merged **CiC**


-- Examples --

let nat = μ nat . #zero:unit | #succ:nat

let even = μ even . 
  #zero:unit | #succ:#succ:even 

let even;odd = μ even;odd . 
  (#zero:unit | #succ:odd) ; #succ:even

let list α = μ list . #nil:unit | #cons:(α;list)

let list_len α = μ list_len . 
  (#nil:unit ; #zero:unit) | 
  ∀ {XS ≤ list α , N ≤ nat} ⟨(XS ; N) ≤ list_len⟩ . (#cons:(α;XS) ; #succ:N) |
  ⊥

- relational type `list_len` is similar to the measure concept in Synquid
- relational types correspond with inductive dependent types and logic programming horn clauses

list_len nil zero
list_len (cons x xs) (succ n) :- list_len xs n 

inductive LL : list α -> nat -> type 
| base : LL nil zero
| step (x : α) : (LL xs n) -> LL (cons x xs) (succ n)


let {4} = #succ:#succ:#succ:#succ:#zero:unit

let list_4 = XS @ XS;{4} ≤ list_len nat

let list_n = n : * => XS @ XS;{n} ≤ list_len nat

%check #cons 1,  #cons 2 #cons 3 , #cons 4 , #nil () : list_4


--------

consider:

```
let x = [1]
-- x : list[int]

let first : (list[str] ; ?) -> list[str]
let first = (a , b) => a 
-- first : (list[str] ; ?) -> list[str]

let _ = first (x, ... 
-- error: list[int] ≤ list[str]
```


basic typing: <br> 
`Γ ⊢ t : τ` <br>

variable
```
(x : τ) ∈ Γ 
---------------------------                        
Γ ⊢ x : τ
```

application
```
Γ ⊢ t₁ : τ₂ -> τ₁
Γ ⊢ t₂ : τ₂'
Γ ⊩ τ₂' ≤ τ₂
------------------------------- 
Γ ⊢ t₁ t₂ : τ₁
```


example: is `first (x, ...` well-typed?
```
Γ ⊢ first : (list[str] ; ?) -> list[str] 
Γ ⊢ (x, ... : ... 
Γ ⊩ ... ≤ (list[str] ; ?)
--------------------------------------------------
Γ ⊢ first (x, ... : ...
```


basic supertyping: <br>
`Γ ⊢ t : τ ≥ τ` <br>

variable
```
(x : τ') ∈ Γ 
Γ ⊩ τ' ≤ τ
---------------------------                        
Γ ⊢ x : τ ≥ τ' 
```

application
```
Γ ⊢ t₁ : ? -> τ₁ ≥ τ₂ -> τ₁'
Γ ⊢ t₂ : τ₂ ≥ _ 
------------------------------- 
Γ ⊢ t₁ t₂ : τ₁ ≥ τ₁'
```


example: is `first (x, ...` well-typed?
```
(x : list[int]) ∈ Γ 
Γ ⊩ list[int] ≤ list[str]
--------------------------------------------------------------------
Γ ⊢ x : list[str] ≥ list[int]
```

consider:
```
let x = [] 
-- x : (∀ α ≤ ? . list[α])

let first : list[str] ; ? -> list[str] 
let first = (a , b) => a 
-- first : (list[str] ; ?) -> list[str]

let _ = first (x, x)  
-- ok 
```

polymorphic supertyping: <br>
`Γ ⊢ t : τ ≥ τ` <br>

variable
```
(x : ∀ Δ . τ') ∈ Γ 
Γ ⊩ (∃ Δ . τ') ≤ τ
---------------------------                        
Γ ⊢ x : τ ≥ ∃ Δ . τ'
```


example: is `first(x, x)` well-typed?
```
(x : ∀ α ≤ ? . list[α]) ∈ Γ 
Γ ⊩ (∃ α ≤ ? . list[α]) ≤ list[str]
--------------------------------------------------------------------
Γ ⊢ x : list[str] ≥ (∃ α ≤ ? . list[α])
```



consider:
```
let x = [] 
-- x : (∀ α ≤ ? . list[α])

let first : list[str] ; ? -> list[str] 
let first = (a , b) => a 
-- first : (list[str] ; ?) -> list[str]

let _ = first (x, x)  
-- ok 
-- treat first as a constraint on the type of x
-- strict option. x : list[str] 
-- lenient option. x : ∃ α . list[str | α]

let y = x ++ [4]
-- ++ : ∀ α ≤ ? . list[α] ; list[α] -> list[α]
-- strict option. error: list[int] ≤ list[str] 
-- lenient option. x : ∃ α . list[str | α]
```



supertyping + constraints: <br>
`Γ ; C ⊢ t : τ ≥ τ ; C` <br>
`Γ ; C ⊩ C` <br>

variable
```
(x : ∀ Δ ⟨D⟩. τ') ∈ Γ 
Γ ; C ⊩ ∃ Δ ⟨D ∧ τ' ≤ τ⟩
-----------------------------------------------------             
Γ ; C ⊢ x : τ ≥ ∃ Δ . τ' ; (∃ Δ ⟨D ∧ τ' ≤ τ⟩)
```
Note: cumbersome redundancy between supertyping and constraints
Note: type information may not be readable from constraints

supertyping * constraints, simple: <br>
`Γ ; C ⊢ t : τ ≥ τ` <br>
`Γ ; C ⊩ τ ≤ τ` <br>

variable
```
(x : ∀ Δ ⟨D⟩. τ') ∈ Γ 
Γ ; C ⊩ (∃ Δ ⟨D⟩ .τ') ≤ τ
-----------------------------------------------------             
Γ ; C ⊢ x : τ ≥ ∃ Δ ⟨D ∧ τ' ≤ τ₁⟩ . τ'
```
Note: cumbersome redundancy between supertyping and constraints
Note: type information may not be readable from constraints


supertyping * constraints, eager unification: <br>
`Γ ; C ⊢ t : τ ≥ τ` <br>
`Γ ; C ⊩ τ ≤ τ ~> Δ ; D` <br>

variable
```
(x : ∀ Δ ⟨D⟩. τ') ∈ Γ 
Γ ; C ⊩ (∃ Δ ⟨D⟩ .τ') ≤ τ ~> Δ' ; D'
-----------------------------------------------------             
Γ ; C ⊢ x : τ ≥ ∃ Δ' ⟨D'⟩ . τ'
```
Note: type information readable in incomplete program 


example: strict option
```
(x : ∃ α ≤ ? . list[α]) ∈ Γ 
Γ ⊩ (∃ α ≤ ? . list[α]) ≤ list[str] ~> α ≤ str
--------------------------------------------------------------------
Γ ⊢ x : list[str] ≥ (∃ α ≤ str . list[α])
```


example: lenient option
```
(x : ∃ α ≤ ? . list[α]) ∈ Γ 
Γ ⊩ (∃ α ≤ ? . list[α]) ≤ list[str] ~> α ≤ (str | α)
--------------------------------------------------------------------
Γ ⊢ x : list[str] ≥ (∃ α ≤ (str | α) . list[α])
```


---------


-- syntax

l, x, α ∈ String                  symbol

cs ::=                            cases
  case t => t                     case singleton 
  cs case t => t                  cases extended 

fs ::=                            fields 
  .l t                            field singleton 
  fs .l t                         fields extended 

t ::=                             term
  _                               irrelevant pattern / inferred expression
  x                               variable expression / pattern
  ()                              unit expression / pattern
  #l t                            variant expression / pattern
  match t cs                      pattern matching 
  fs                              record expression / pattern
  t.l                             record projection
  x : τ => t                      function abstraction
  t t                             function application
  α <: τ => t                     type abstraction
  t τ                             type application 
  let t : τ = t in t              binding
  hide τ in t                     type packing 
  let α with t = t in t           type unpacking
  fix t                           recursion

τ ::=                             type
  α                               variable type
  ?                               dynamic type
  unit                            unit type
  #l : τ                          variant type
  .l : τ                          field type
  τ -> τ                          implication type 
  τ & τ                           intersection type
  τ | τ                           union type
  ∀ Δ ⟨C⟩ . τ                     universal schema 
  ∃ Δ ⟨C⟩ . τ                     existential schema 
  μ α . t                         inductive type
  α <: τ => τ                     typerator abstraction
  τ τ                             typerator application

κ ::=                             kind
  *τ                              ground kind
  κ --> κ                         higher kind

Γ ::=                             context
  ·                               empty context
  Γ, x : τ                        context extended with indentifier and its type 
  Γ, α <: τ                       context extended with indentifier and its super type 


-- syntactic sugar -- 
t₁ , t₂                           .left t₁ .right t₂               -- product

t₁ => t₂                          t₁ : ? => t₂                     
let t₁ = t₂ in t₃                 let t₁ : ? = τ₂ in t₃


t₁ ; t₂                           (.left : t₁) ∧ (.right : t₂)     -- product type


-- semantics --

----------------------------------------------------------------------------

Γ ⊢ τ ≃ τ                                type equivalence

α₁ <: τ ∈ Γ                              
α₂ <: τ ∈ Γ                              
------------                              variable 
Γ ⊢ α₁ ≃ α₂                             


-----------
Γ ⊢ τ ≃ τ                                refl


Γ ⊢ τ₂ ≃ τ₁                              
-----------                               symm
Γ ⊢ τ₁ ≃ τ₂                               


Γ ⊢ τ₁ ≃ τ                              
Γ ⊢ τ ≃ τ₂                              
-----------                               trans
Γ ⊢ τ₁ ≃ τ₂                               


Γ ⊢ τ₁ ≃ τ₃                              
Γ ⊢ τ₂ ≃ τ₄                              
------------------------                     implication
Γ ⊢ τ₁ -> τ₂ ≃ τ₃ -> τ₄                               


Γ ⊢ τ₁ ≃ τ₃                              
Γ, α₁ <: τ₃, α₂ <: τ₃ ⊢ τ₂ ≃ τ₄                              
fresh α₁
fresh α₂
-----------------------------------------    universal
Γ ⊢ (∀ α₁ <: τ₁ . τ₂) ≃ (∀ α₂ <: τ₃ . τ₄)                               


Γ ⊢ τ₁ ≃ τ₃                              
Γ, α₁ <: τ₃, α₂ <: τ₃ ⊢ τ₂ ≃ τ₄                              
fresh α₁
fresh α₂
-----------------------------------------    existential
Γ ⊢ (∃ α₁ <: τ₁ . τ₂) ≃ (∃ α₂ <: τ₃ . τ₄)                               


Γ ⊢ τ₁ ≃ τ₃                              
Γ, α₁ <: τ₃, α₂ <: τ₃ ⊢ τ₂ ≃ τ₄                              
fresh α₁
fresh α₂
-----------------------------------------    typerator abstraction
Γ ⊢ (α₁ <: τ₁ => τ₂) ≃ (α₂ <: τ₃ => τ₄)                                


Γ ⊢ τ₁ ≃ τ₃                                
Γ ⊢ τ₂ ≃ τ₄                                
-----------------------------------------    typerator application
Γ ⊢ τ₁ τ₂ ≃ τ₃ τ₄                                


fresh α
-----------------------------------------    typerator abstraction application
Γ ⊢ (α <: τ₁ => τ₂) τ₃ ≃ τ₄[α → τ₃]                                


----------------------------------------------------------------------------


Γ ⊢ τ :: κ                                kinding


α <: τ ∈ Γ
Γ ⊢ τ :: κ 
------------                              variable
Γ ⊢ α :: κ 


Γ ⊢ τ₁ :: κ 
Γ, α <: τ₁ ⊢ τ₂ <: τ₁  
--------------------------------------      typerator abstraction
Γ ⊢ α <: τ₁ => τ₂ :: *τ₁ --> κ 


Γ ⊢ τ₁ :: *τ --> κ 
Γ ⊢ τ₂ <: τ   
Γ ⊢ τ :: κ 
------------------------------            typerator application
Γ ⊢ τ₁ τ₂ :: κ 


Γ ⊢ τ₁ :: *? 
Γ ⊢ τ₂ :: *?
------------------------------            implication
Γ ⊢ τ₁ -> τ₂ :: *?


Γ ⊢ τ₁ :: κ 
Γ, α <: τ₁ ⊢ τ₂ :: *? 
------------------------------            universal
Γ ⊢ ∀ α <: τ₁ . τ₂ :: *? 


Γ ⊢ τ₁ :: κ 
Γ, α <: τ₁ ⊢ τ₂ :: *? 
------------------------------            existential
Γ ⊢ ∃ α <: τ₁ . τ₂ :: *? 


---------------------------------------------------------------------------------


Γ ⊢ τ <: τ                                consistent subtyping


----------------                          refl
Γ ⊢ τ <: τ


Γ ⊢ τ :: *?
----------------                          dyno_right
Γ ⊢ τ <: ? 


Γ ⊢ τ :: *?
----------------                          dyno_left
Γ ⊢ ? <: τ 


Γ ⊢ τ₁ <: τ 
Γ ⊢ τ <: τ₂
τ :: u
τ ≠ ?
--------------                            trans
Γ ⊢ τ₁ <: τ₂  


α <: τ ∈ Γ 
----------------                          variable
Γ ⊢ α <: τ  


Γ ⊢ τ₁ :: u
Γ ⊢ τ₃ :: u
Γ ⊢ τ₃ <: τ₁ 
Γ, α₁ <: τ₃, α₂ <: τ₃ ⊢ τ₂ <: τ₄ 
fresh α₁
fresh α₂
-----------------------------------------   universal
Γ ⊢ (∀ α₁ <: τ₁. τ₂)  <: (∀ α₂ <: τ₃. τ₄)


Γ ⊢ τ₁ :: u
Γ ⊢ τ₃ :: u
Γ ⊢ τ₁ <: τ₃ 
Γ, α₁ <: τ₁, α₂ <: τ₁ ⊢ τ₂ <: τ₄ 
fresh α₁
fresh α₂
-----------------------------------------   existential
Γ ⊢ (∃ α₁ <: τ₁. τ₂) <: (∃ α₂ <: τ₃. τ₄)


Γ ⊢ τ₁ :: u
Γ ⊢ τ₃ :: u
Γ ⊢ τ₃ <: τ₁
Γ, α₁ <: τ₃, α₂ <: τ₃ ⊢ τ₂ <: τ₄ 
fresh α₁
fresh α₂
----------------------------------------- typerator abstraction
Γ ⊢ (α₁ <: τ₁ => τ₂) <: (α₂ <: τ₃ => τ₄)


Γ ⊢ τ₁ <: τ₂
----------------------------------------- typerator application 
Γ ⊢ τ₁ τ <: τ₂ τ


Γ ⊢ convariant τ
Γ ⊢ τ₁ <: τ₂
----------------------------------------- typerator convariant 
Γ ⊢ τ τ₁ <: τ τ₂


Γ ⊢ contravariant τ
Γ ⊢ τ₂ <: τ₁
----------------------------------------- typerator contravariant
Γ ⊢ τ τ₁ <: τ τ₂


Γ ⊢ τ₁ :: u
Γ ⊢ τ₂ :: u
Γ ⊢ τ₁ ≃ τ₂ 
-------------------------                 eq
Γ ⊢ τ₁ <: τ₂


Γ ⊢ τ₃ <: τ₁ 
Γ ⊢ τ₂ <: τ₄ 
-------------------------                 implication
Γ ⊢ τ₁ -> τ₂ <: τ₃ -> τ₄


Γ ⊢ τ₁ <: τ₂  
------------------                        field
Γ ⊢ .l τ₁ <: .l τ₂  


Γ ⊢ τ₁ <: τ₂  
--------------------                      variant 
Γ ⊢ #l τ₁ <: #l τ₂  


------------------                        union_left
Γ ⊢ τ₁ <: τ₁ ∨ τ₂  


------------------                        union_right
Γ ⊢ τ₂ <: τ₁ ∨ τ₂  


Γ ⊢ τ₁ <: τ   
Γ ⊢ τ₂ <: τ  
------------------                        union 
Γ ⊢ τ₁ ∨ τ₂ <: τ 


-------------------                       intersection_left
Γ ⊢ τ₁ ∧ τ₂ <: τ₁  


-------------------                       intersection_right
Γ ⊢ τ₁ ∧ τ₂ <: τ₂  


Γ ⊢ τ <: τ₁  
Γ ⊢ τ <: τ₂  
------------------                        intersection
Γ ⊢ τ <: τ₁ ∧ τ₂  



--------------------------------------------------------------------------------------
constraint solving/unification 

Γ ; C ⊩ τ ≤ τ ~> Δ ; D

- subtyping corresponds to predicate defined by horn clauses
- existential on the right: unify + backchain
- existential on the left: differs from prolog/backchaining in that existential may be nested within predicate 
- solving is similar to synquid 
  - due to eager unification with constraints in subptyping producing implication of constraints 
- solving is simpler than synquid by avoiding separate language of refinements 
- termination condition: constraints cannot be reduced  

- recycling renamed constraints happens at existential  

- constraints in existential of subtype e.g ∃ Δ' ⟨D'⟩ τ' ≤ ∃ Δ ⟨D⟩ τ
  - are reduced to  Δ'; Δ ⊩ D' ∧ D ∧ τ' ≤ τ
  - the subtyping is sufficient to subsume the implication D' --> D

- a constraint on a single variable is simply recorded without recylcing
- strictly record type variable in α ≤ τ as (α → τ & Β)
  - {α → nat & β, β → ?} ⊩ α ≤ even ==> nat & β ≤ even ==> nat ≤ even ∨ β ≤ even ==> nat ≤ even ∨ β ≤ even  ==> β ≤ even
  - {α → nat & β, β → ?} ⊩ α ≤ int ==> nat & β ≤ int ==> nat ≤ int ∨ β ≤ int ==> nat ≤ int ∨ β ≤ int
- leniently record type variable in τ ≤ α as (α → τ | β)
  - τ ≤ α, [β → ?, α → τ | β]
    - α ≤ X ==> (τ | β) ≤ X ==> (τ | ?) ≤ X ==> (τ ≤ X) ==> [Y → ?, X → [τ | Y]] 
      - X ≤ τ ==> τ | ? ≤ τ ==> False
    - X ≤ τ ==> [X → τ]
      - α ≤ X ==> τ | ? ≤ τ ==> False



- generalize any unbound variables in both input and output of function abstraction
- convert any unbound variables only in return type to ⊥ type. 



- solving generates solutions to type variables
  - it does not generate new constraints

- unions/intersections in relation to inductive type?
  - (τ₁ | τ₂) ≤ (μ Z . τ) ==> τ₁ ≤ (∀ X ⟨(X | τ₂) ≤ unroll(μ Z . τ)⟩ . X) ∧ τ₂ ≤ (∀ Y ⟨(τ₁ | Y) ≤ unroll(μ Z . τ)⟩ . Y)
  - (τ₁ & τ₂) ≤ (μ Z . τ) ==> τ₁ ≤ (∀ X ⟨(X & τ₂) ≤ unroll(μ Z . τ)⟩ . X) ∧ τ₂ ≤ (∀ Y ⟨(τ₁ & Y) ≤ unroll(μ Z . τ)⟩ . Y)
  - (τ₁ ; τ₂) ≤ (μ Z . τ) ==> τ₁ ≤ (∀ X ⟨(X ; τ₂) ≤ unroll(μ Z . τ)⟩ . X) ∧ τ₂ ≤ (∀ Y ⟨(τ₁ ; Y) ≤ unroll(μ Z . τ)⟩ . Y)
  - breaking pairs into existential types allows saving constraints on variables that cannot be reduced 
  - unrolling inside existential type avoids diverging in case pair cannot be unified with inductive type 
  - example
    - (#nil:unit ; #zero:unit) ≤ _ ==> 
      #nil:unit ≤ (∀ X ⟨(X ; #zero:unit) ≤ ((#nil:unit ; #zero:unit) | ...) ⟩ . X) ==>
    - (X ; Y ) ≤ _ ==> 
      X ≤ (∀ X ⟨(X ; Y) ≤ ((#nil:unit ; #zero:unit) | ...) ⟩ . X) ==>
      - X ≤ list ==>
        (X' ; Y) ≤ ((#nil:unit ; #zero:unit) | ...) ∧  X' ≤ list ==>
        (list ; Y) ≤ ((#nil:unit ; #zero:unit) | ...) ==>
        (list ; Y) ≤ (#nil:unit ; #zero:unit) ∨ (list ; Y) ≤ (#nil:unit ; #zero:unit) ==>
        FAIL # this constraint does not refine existing upper bound
      - order matters? X ≤ τ₁ ∧ X ≤ τ₂; do we need intersection?


    - (.l X & .r Y ) ≤ (μ Z . τ) ==> 
      .l X ≤ (∀ X' ⟨X' & .r Y ≤ unroll(μ Z . τ)⟩ . X') ∧ .r Y ≤ (∀ Y' ⟨.l X & ; Y') ≤ unroll(μ Z . τ)⟩ . Y') ==>
      ... ==>
      .l X ≤ X' ∧ X' & .r Y ≤ unroll(μ Z . τ) ==>
      {X' → .l X | β} ⊢ X' & .r Y ≤ unroll(μ Z . τ) ==> 
      {X' → .l X | β} ⊢ X' & .r Y ≤ (#nil ; #zero) | (#cons XS ; #succ N) ==> 
      {X' → .l X | β} ⊢ (l. X | β) & (.r Y) ≤ (#nil ; #zero) ==> 
      {X' → .l X | β} ⊢ (l. X | β) & (.r Y) ≤ (#nil ; #zero) ==> 
      {X' → .l X | β} ⊢ (l. X | β) & (.r Y) ≤ (#nil ; #zero) ==> 
      -- BAD!!! infinite recursion 
      -- what is the precise reason for divergence?
        -- we never reduce one side to a variable
      -- must pattern match on union before separating intersection

- inductive type may only relate to variants and records
- treat record type as a special canonical form, such that a record of variables may relate to inductive type
  - if there is an inductive relation with intersection, then intersection must be a record



-- intersection: must break right side items into conjuctive parts before disjunctive parts
  - raise the supertype as much as possible
  - {x, y} & {z} <: {x, y, z} ==> {x, y} & {z} <: {x} & {y} & {z} ==>
    ({x, y} & {z} <: {x}) ∧ ({x, y} & {z} ≤ {y}) ∧ ({x, y} & {z} ≤ {z})
  - {x, y} & {z} <: {x, y, z} ==> ({x, y} <: {x, y, z}) ∨  ({z} <: {x, y, z})

-- union: must break left side items into conjuctive parts before disjunctive parts
  - lower the subtype as much as possible
  - #x | # y | #z <: #x | # y | #z ==>
      (#x <: #x | # y | #z) ∧ (#y <: #x | # y | #z)
  - #x | # y | #z <: #x | # y | #z ==>
      (#x | # y | #z <: #x) ∨ (#x | # y | #z <: #y)
  


- occurs check: turn type in circular constraint into inductive type
  - ML datatypes avoid circular constraint by inferring type from tag
  - #succ α <: α ==> {α → (μ α . #succ α | β), β → ?}

- well-formed inductive type (μ α . τ) check

- roll
  - τ' ≤ (μ Z . τ) ==> τ' ≤ unroll(μ Z . τ) ==> τ' ≤ τ[μ Z . τ]
  - invariant: τ[(μ Z . τ)] ≤ (μ Z . τ)
- unroll
  - (μ Z . τ') ≤ τ ==> uroll(μ Z . τ') ≤ τ ==> τ'[μ Z . τ'] ≤ τ 
  - invariant: (μ Z . τ) ≤ τ[(μ Z . τ)]


theorems:
  - completeness: if alorithm produces some type output then constraint typing holds on output type
  - soundness: if constraint typing holds on a type then algorithm succeeds with type as input


-/