/-

-- title --
type assisted program synthesis for dynamic languages


-- Goals --
1. strict/unannotated
  - reject erroneous programs with unannotated types
2. strict/incomplete
  - reject erroneous incomplete programs with type annotations 
  - remove erroneous programs from search space for synthesis
3. lenient/unannotated 
  - accept error-free programs with incomplete types
4. lenient/incomplete
  - accept error-free incomplete programs with type annotations 
  - include interesting programs in search space for synthesis

-- Concepts --
- correctness: strict vs lenient
  - strict: reject programs with errors 
  - lenient: accept programs without errors 

- elaboration: unannotated types vs incomplete programs 
  - unannotated types: infer types from terms
  - incomplete programs: synthesizes terms from types

- kinds 
  - kinding serves two purposes: 
    - ensure wellformedness of types/typerators
    - ensure certain arity of types/typerators 
  - a kind categorizes a type or typerator by arity **Fω** - https://xavierleroy.org/CdF/2018-2019/2.pdf
  - keeping kinds syntactically distinct from types is useful for subtyping syntax in bounded quantification/typerator abstraction

- A scheme is a type that quantifies over types 
  - predicativity is recognized by treating quantifiers as large types belonging to □  
  - predicativity is controlled by universes. **1ml** by Andreas Rossberg - https://people.mpi-sws.org/~rossberg/1ml/1ml.pdf

- relational types relate a type to parts of some relation 
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


-- other unused concepts --

- refinement types are not necessary (yet)
  - inference based on subtyping relation **ML refinement types**
    - ML refinement types of user-defined datatypes (variant types) are explicitly declared
      - datatype creates a named supertype (upper) bound. A
      - any type defined in terms of of the datatype's subtypes is defined as a datatype's subtype 
    - ML refinement types' intersections of user-defined types are inferred from subtyping relations
    - ML refinement types do not relate type to parts of a product type 

- collapsing types and terms is not necessary (yet)
  - various abstraction and composition portions of types and terms are merged **CiC**


-- Examples --

let nat = μ nat . #zero:unit ∨ #succ:nat

let even = μ even . 
  #zero:unit ∨ 
  #succ:#succ:even 

let even;odd = μ even;odd . 
(
  #zero:unit ∨ 
  #succ:odd
);(
  #succ:even
)

let list α = μ list . #nil:unit ∨ #cons:(α;list)

let list_len α = μ list_len . 
  (#nil:unit ; #zero:unit) ∨ 
  (#cons:(α;XS) ; #succ:N) @ XS;N <: list_len 

- relational type `list_len` is similar to the measure concept in Synquid

- inductive dependent types have an isomorphic form
inductive LL : list α -> nat -> type 
| base : LL nil zero
| step (x : α) : (LL xs n) -> LL (cons x xs) (succ n)


let {4} = #succ:#succ:#succ:#succ:#zero:unit

let list_4 = XS @ XS;{4} <: list_len nat

let list_n = n : * => XS @ XS;{n} <: list_len nat

%check #cons 1,  #cons 2 #cons 3 , #cons 4 , #nil () : list_4


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
  {τ, t} as ∃ α . τ               type packing 
  let {α, t} = t in t             type unpacking
  fix t                           recursion

τ ::=                             type
  α                               variable type :: *
  ?                               dynamic type :: *
  unit                            unit type :: *
  #l : τ                          variant type :: *
  .l : τ                          field type :: *
  τ -> τ                          implication type :: * 
  τ ∧ τ                           intersection type :: *
  τ ∨ τ                           union type :: *
  ∀ α <: τ . τ                    universal schema :: □ 
  ∃ α <: τ . τ                    existential schema :: □ 
  μ α . t                         inductive type :: *
  α <: τ => τ                     typerator abstraction
  τ τ                             typerator application
  τ @ τ <: τ                      relational type :: * where τ :: * 

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
---------------------------------------   universal
Γ ⊢ (∀ α₁ <: τ₁. τ₂)  <: (∀ α₂ <: τ₃. τ₄)


Γ ⊢ τ₁ :: u
Γ ⊢ τ₃ :: u
Γ ⊢ τ₁ <: τ₃ 
Γ, α₁ <: τ₁, α₂ <: τ₁ ⊢ τ₂ <: τ₄ 
fresh α₁
fresh α₂
---------------------------------------   existential
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



--------------------------------------------------------------------------


Γ ⊢ t : τ :> τ                            type constraint strenthening 


x : τ₂ ∈ Γ 
τ₂ <: τ₁
------------------                        variable
Γ ⊢ x : τ₁ :> τ₂ 



Γ ⊢ t₁ : ? -> τ₁ :> τ₂ -> τ₃ 
Γ ⊢ t₂ : τ₂ :> τ₄
-------------------------------            function application
Γ ⊢ t₁ t₂ : τ₁ :> τ₃


-- from checking to HM strengening -- 


Γ ⊢ τ₁ :: *?
Γ, x : τ₁ ⊢ t₂ : τ₂ 
-----------------------------------       function abstraction
Γ ⊢ x : τ₁ => t₂ : τ₁ -> t₂ 


----------------------------------------------------------------------------


-/