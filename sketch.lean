-- title --
/-
type directed program synthesis for dynamic languages
-/

-- introduction --
/-


Dualities
1. correctness: strict vs lenient
  - strict: reject programs with errors 
  - lenient: accept programs without errors 
2. elaboration: forward vs backward 
  - forward: incomplete types; infer types from terms
  - backward: incomplete terms; synthesizes terms from types

Goals
1. strict/forward
  - reject erroneous programs with incomplete types
2. strict/backward
  - reject erroneous incomplete programs with type annotations 
3. lenient/forward: 
  - accept error-free programs with incomplete types
4. lenient/backward
  - accept error-free incomplete programs with type annotations 

-/

-- syntax
/-

l, x, α ∈ String                     symbol

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
  t : τ => t                      function abstraction
  t t                             function application
  α <: τ => t                     type abstraction
  t[τ]                            type application 
  let t : τ = t in t              binding
  {τ, t} as ∃ α . τ               type packing 
  let {α, t} = t in t             type unpacking
  fix t                           recursion

τ ::=                             type
  α                               variable type : *
  ?                               dynamic type : *
  unit                            unit type : *
  #l : τ                          variant type : *
  .l : τ                          field type : *
  τ -> τ                          implication type where τ : * or higher kind where τ : **
  τ ∧ τ                           intersection type : *
  τ ∨ τ                           union type : *
  ∀ α <: τ . τ                    universal schema : **
  ∃ α <: τ . τ                    existential schema : **
  μ α . t                         inductive type : *
  α => τ                          type constructor abstraction
  τ τ                             type constructor application
  τ @ τ <: τ                      refinement type : * where τ : * 

Γ ::=                             context
  ·                               empty context
  Γ, x : τ                        context extended with indentifier and its type 
  Γ, α <: τ                       context extended with indentifier and its super type 


-- syntactic sugar -- 
t₁ , t₂                           .left t₁ .right t₂               -- product

t₁ => t₂                          t₁ : ? => t₂                     
let t₁ = t₂ in t₃                 let t₁ : ? = τ₂ in t₃


t₁ ; t₂                           (.left : t₁) ∧ (.right : t₂)     -- product type


- kinds
  - a kind categorizes a type or type constructor by arity **Fω** - https://xavierleroy.org/CdF/2018-2019/2.pdf
  - a term satifies a type of higher kind if  it type checks with all of its arguments instantiated with the dynamic type 
  - it is useful for safely generalizing over type construcotrs rather than merely types 
  - τ : κ : **, i.e. a type belongs to a kind, which belongs to ** 
  - τ => τ : κ -> κ : **, i.e. a type constructor belongs to a kind, which belongs to ** 

- A schema is a type that quantifies over types 
  - predicativity is recognized by treating quantifiers as large types belonging to **
  - predicativity is controlled by universes. **1ml** by Andreas Rossberg - https://people.mpi-sws.org/~rossberg/1ml/1ml.pdf
  - universal and existential types quantify over types of kind *, resulting in types of kind **
  - these type quantifiers are primitive in this logic with refinement types, rather than dependent types
  - in a stronger dependently typed / higher kinded logic, these types would be subsumed by implication 

- relational types relate a type to parts of some relation 
  - relate a type to parts of a product type via product subtyping **novel** 
    - obviate the need for outsourcing to SMT solver, 
    - allow reusing definitions for both checking and constructing subtypes 
    - avoid dependencies on values

  - relation as booean expression is not necessary (yet)
    - boolean expressions relate parts of types using predicate expressions rather than subtypings **liquid types**
    - liquid types rely on SMT solvers check refinements
    - liquid types may have dependencies on values

- refinement types are not necessary yet
  - inference based on subtyping relation **ML refinement types**
    - ML refinement types of user-defined datatypes (variant types) are explicitly declared
      - datatype creates a named supertype (upper) bound. A
      - any type defined in terms of of the datatype's subtypes is defined as a datatype's subtype 
    - ML refinement types' intersections of user-defined types are inferred from subtyping relations
    - ML refinement types do not relate type to parts of a product type 

- collapsing types and terms is not necessary (yet)
  - various abstraction and composition portions of types and terms are merged **CiC**



-/

-- example --
/-

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


let {4} = #succ:#succ:#succ:#succ:#zero:unit

let list_4 = XS @ XS;{4} <: list_len nat

let list_n = n : * => XS @ XS;{n} <: list_len nat

%check 1 :: 2 :: 3 :: 4 :: #nil : list_4

-/

-- semantics --
/-

Γ ⊢ τ <: τ                                consistent subtyping


----------------                          refl
Γ ⊢ τ ~ τ


----------------                          dyno_right
Γ ⊢ τ ~ ? 


----------------                          dyno_left
Γ ⊢ ? ~ τ 


Γ ⊢ τ₁ <: τ 
Γ ⊢ τ <: τ₂
τ ≠ ?
--------------                            trans
Γ ⊢ τ₁ <: τ₂  


α <: τ ∈ Γ 
----------------                          variable
Γ ⊢ α <: τ  


Γ ⊢ τ₃ <: τ₁ 
Γ, α <: τ₃ ⊢ τ₂ <: τ₄ 
---------------------------------------   universal
Γ ⊢ (∀ α <: τ₁. τ₂)  <: (∀ α <: τ₃. τ₄)


Γ ⊢ τ₁ <: τ₃ 
Γ, α <: τ₁ ⊢ τ₂ <: τ₄ 
---------------------------------------   existential
Γ ⊢ (∃ α <: τ₁. τ₂)  <: (∃ α <: τ₃. τ₄)


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


- too lenient vs too strict in the context of synthesis
  - too lenient would result in a large search space 
  - too strict would prevent generating intersting idiomatic programs

- subtyping incorporates dynamic type 
  - combine consistency with subtyping **gradual typing**
    - gradual typing supplements subtyping with masking or separate consistency relation
  - non-transitive dynamic subtyping **novel** 
    - prevents everything from subtyping 
      e.g.
      X <: ?    ? <: T
      ------------------
            X <: T  


Γ ⊢ t : τ :> τ                    type strengthening


- propagate types down, delay subsumption 
  - propgate types down, and infer types up **bidrectional typing**
  - always propagate down, even if inferring upward **roundtrip typing**
  - propagate dynamic types **novel**

Γ ⊢ t : τ :> τ ~> t               term synthesis

Γ C ⊢ ...                         constraint typing

Γ C ⊢ τ <: x = τ                  constraint solving

- find some super type satisfying constraints
  - find the least super type satsifying constraints **HM(X)**
  - find a somewhat lenient super type satsifying constraints **novel**

-/