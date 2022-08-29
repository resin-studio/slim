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

l, x ∈ String                     symbol

cs ::=                            cases
  case t => t                     case singleton 
  cs case t => t                  cases extended 

fs ::=                            fields 
  .l t                            field singleton 
  fs .l t                         fields extended 

t ::=                             term
  _                               irrelevant pattern / inferred expression
  t : t                           typed pattern where τ : κ : **
  x                               variable expression / pattern
  ()                              unit expression / pattern
  #l t                            variant expression / pattern
  match t cs                      pattern matching 
  fs                              record expression / pattern
  t.l                             record projection
  t : t => t                      function abstraction
  t t                             function application
  let t : t = t in t              binding
  fix t                           recursion

  ?                               dynamic type : *
  unit                            unit type : * 
  #l : t                          variant type : *
  .l : t                          field type : *
  t -> t                          implication type where τ : * or higher kind where τ : **
  t ∧ t                           intersection type : *
  t ∨ t                           union type : *
  ∀ x : t . t                     universal schema : **
  ∃ x : t . t                     existential schema : **
  μ x . t                         inductive type : *
  t @ t <: t                      refinement type : * where τ : * 
  *                               ground kind : **

- collapse the syntax of type with term
  - collapse type constructors, polymorphic terms, and lambdas into `t => t` **Cic** 
  - consistent with Python's unstratified syntax
-/


-- syntactic sugar -- 
/-
t₁ , t₂                           .left t₁ .right t₂               -- product
t₁ ; t₂                           (.left : t₁) ∧ (.right : t₂)     -- product type

t₁ => t₂                          t₁ : ? => t₂                     
let t₁ = t₂ in t₃                 let t₁ : ? = t₂ in t₃

-/

-- canonical form --
/-

vfs ::=                           value fields
  .l v                            field singleton 
  vfs .l v                        fields extended 

v :: =                            value
  ()                              unit
  #l v                            variant
  vfs                             record

τ ::=                             type
  x                               variable type : *
  ?                               dynamic type : *
  unit                            unit type : *
  #l : τ                          variant type : *
  .l : τ                          field type : *
  τ -> τ                          implication type where τ : * or higher kind where τ : **
  τ ∧ τ                           intersection type : *
  τ ∨ τ                           union type : *
  ∀ x : τ . τ                     universal schema : **
  ∃ x : τ . τ                     existential schema : **
  μ x . t                         inductive type : *
  τ @ τ <: τ                      refinement type : * where τ : * 
  *                               ground kind : **

Γ ::=                             context
  ·                               empty context
  Γ, x : τ                        context extended with indentifier and its type 



- A schema is a semantic notion that categorizes generic type forms 
  - predicativity is recognized by treating quantifiers as large types belonging to **
    - unlike kinds which also belong to **, only terms, not types belong to 
    - predicativity is controlled by universes. **1ml** by Andreas Rossberg - https://people.mpi-sws.org/~rossberg/1ml/1ml.pdf
  - universal and existential types quantify over types of kind *, resulting in types of kind **
  - these type quantifiers are primitive in this logic with refinement types, rather than dependent types
  - in a stronger dependently typed / higher kinded logic, these types would be subsumed by implication 
- A kind is a semantic notion that categorizes type forms of varying arity 
  - a kind categorizes a type or type constructor by arity **Fω** - https://xavierleroy.org/CdF/2018-2019/2.pdf
  - τ : κ : **, i.e. a type belongs to a kind, which belongs to ** 
  - τ => τ : κ -> κ : **, i.e. a type constructor belongs to a kind, which belongs to ** 

- refinement types / relational types
  - a special kind of subtyping
  - refine a type in terms of subtypings **refinement types in ML**
  - relate content of a type to other values **liquid types**
    - liquid types refine using predicate expressions, rather than typings
    - liquid types rely on SMT solvers check refinements
  - relate content of a type AND refine types in terms of subtypings **novel** 
    - obviate the need for outsourcing to SMT solver, 
    - allow reusing definitions for both checking and refinement
    - avoid dependency on values

-/

-- example --
/-

let list = α : * => μ list . #nil:unit ∨ #cons:(α;list)

let nat = μ nat . #zero:unit ∨ #succ:nat

let list_len = α : * => μ list_len . 
  (#nil:unit ; #zero:unit) ∨ 
  (#cons:(α;XS) ; #succ:N) @ XS;N <: list_len 

-- list_len <: list;nat
-- #nil(), #zero() : list_len
-- (a,xs,n => #cons(a, xs), #succ n) : α;XS;N -> list_len 


let {4} = #succ:#succ:#succ:#succ:#zero:unit

let list_4 = XS @ XS;{4} <: list_len nat

let list_n = n : * => XS @ XS;{n} <: list_len nat

%check 1 :: 2 :: 3 :: 4 :: #nil : list_4

-/

-- semantics --
/-

Γ ⊢ τ <: τ                        consistent subtyping


----------------                  dyno_right
Γ ⊢ τ ~ ? 


----------------                  dyno_left
Γ ⊢ ? ~ τ 


Γ ⊢ τ₁ <: τ 
Γ ⊢ τ <: τ₂
τ ≠ ?
--------------                    trans
Γ ⊢ τ₁ <: τ₂  


τ₁ <: τ₂  
------------------                field
Γ ⊢ .l τ₁ <: .l τ₂  


Γ ⊢ τ₁ <: τ₂  
--------------------              variant 
Γ ⊢ #l τ₁ <: #l τ₂  


------------------                union_left
Γ ⊢ τ₁ <: τ₁ ∨ τ₂  


------------------                union_right
Γ ⊢ τ₂ <: τ₁ ∨ τ₂  


Γ ⊢ τ₁ <: τ   
Γ ⊢ τ₂ <: τ  
------------------                union 
Γ ⊢ τ₁ ∨ τ₂ <: τ 


-------------------               intersection_left
Γ ⊢ τ₁ ∧ τ₂ <: τ₁  


-------------------               intersection_right
Γ ⊢ τ₁ ∧ τ₂ <: τ₂  


Γ ⊢ τ <: τ₁  
Γ ⊢ τ <: τ₂  
------------------                intersection
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