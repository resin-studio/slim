
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
  #l                              tag expression / pattern
  #l t                            variant expression / pattern
  match t cs                      pattern matching 
  fs                              record expression / pattern
  t.l                             record projection
  t => t                          function abstraction
  t t                             function application
  let t = t in t                  binding
  fix t                           recursion
  ?                               dynamic type : *
  $l                              tag type : *
  #l : t                          variant type : *
  .l : t                          field type : *
  t & t                           intersection type : *
  t | t                           union type : *
  t -> t                          implication type where τ : * or higher kind where τ : **
  μ x . t                         inductive type : *
  ∀ x : t . t                     universal type : ** where x : _ : ** (predicative) or x : ** (impredicative)
  ∃ x : t . t                     existential type : ** where x : _ : ** (predicative) or x : ** (impredicative)
  { t | t : t }                   relational type : * where τ : * 
  *                               ground kind : **
  [t]                             annotation kind where t : [t] <: * : **

- term sugar
  - ⟦(t1 , t2)⟧  ~> (.left ⟦t1⟧, .right ⟦t2⟧)
- collapse the syntax of type with term
  - collapse type constructors, polymorphic terms, and lambdas into `t => t` **Cic** 
  - consistent with Python's unstratified syntax
  - related: **CiC** 
-/

-- canonical form --
/-

vfs ::=                           value fields
  .l v                            field singleton 
  vfs .l v                        fields extended 

v :: =                            value
  #l                              tag
  #l v                            variant
  vfs                             record

τ ::=                             type
  x                               variable type : *
  ?                               dynamic type : *
  $l                              tag type : *
  #l : τ                          variant type : *
  .l : τ                          field type : *
  τ & τ                           intersection type : *
  τ | τ                           union type : *
  τ -> τ                          implication type where τ : * or higher kind where τ : **
  ∀ x : τ . τ                     universal type : ** where x : _ : ** (predicative) or x : ** (impredicative)
  ∃ x : τ . τ                     existential type : ** where x : _ : ** (predicative) or x : ** (impredicative)
  μ x . τ                         inductive type : *
  { t | t : τ }                   relational type : * where τ : * 
  *                               ground kind : **
  [τ]                             annotation kind where τ : [τ] <: * : **
  {v}                             singleton 

Γ ::=                             context
  ·                               empty context
  Γ, x : τ                        context extended with indentifier and its type 

- implication is the same as universal without dependency 
  - τ -> τ  ==  ∀ x : τ . τ where x ∉ τ
- A type is an internal representation 
- A kind is a semantic notion that categorizes both term and type syntax
  - τ : κ : **, i.e. a type belongs to a kind, which belongs to ** 
  - τ => τ : κ -> κ : **, i.e. a type constructor belongs to a kind, which belongs to ** 
  - related: **Fω** - https://xavierleroy.org/CdF/2018-2019/2.pdf
- predicativity is recognized by treating quantifiers as large types belonging to **
  - unlinke kinds which also belong to **, only terms, not types belong to 
  - related work: **1ml** by Andreas Rossberg - https://people.mpi-sws.org/~rossberg/1ml/1ml.pdf
- universal and existential types quantify over types of kind *, resulting in types of kind **
- these type quantifiers are primitive in this weak logic
- in a stronger dependently typed / higher kinded logic, these types would be subsumed by implication 
- composite types defined in terms of subtyping combinators --
  - A ∧ B = (.left : A) & (.right : B)           -- product
  - A ∨ B = (#left : A) | (#right : B)           -- sum
- relational types 
  - a special kind of dependent types with subtyping
  - refine a type in terms of typings **refinement types in ML**
  - relate content of a type to other values **liquid types**
    - liquid types refine using predicate expressions, rather than typings
    - liquid types rely on SMT solvers check refinements
  - relate content of a type AND refine types in terms of typings **novel** 
    - obviate the need for outsourcing to SMT solver, 
    - allow reusing definitions for both checking and refinement
-/

-- example --
/-

let list = α : * => μ list . $nil | #cons:(α ∧ list)

let nat = μ nat . ?zero | #succ:nat

let list_len = α : * => μ list_len . ($nil ∧ $zero) | {(#cons (_ : α, xs), #succ n) | (xs, n) : list_len}

let 4 = #succ (#succ (#succ (#succ $zero)))

let list_4 = {xs | (xs, 4) : list_len nat}

%check 1 :: 2 :: 3 :: 4 :: $nil : list_4

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


Γ ⊢ τ <: τ₁
------------------                union_left
Γ ⊢ τ <: τ₁ | τ₂  


Γ ⊢ τ <: τ₂
------------------                union_right
Γ ⊢ τ <: τ₁ | τ₂  


Γ ⊢ τ₁ <: τ   
Γ ⊢ τ₂ <: τ  
------------------                union 
Γ ⊢ τ₁ | τ₂ <: τ 


Γ ⊢ τ₁ <: τ
-------------------               intersection_left
Γ ⊢ τ₁ & τ₂ <: τ  


Γ ⊢ τ₂ <: τ
-------------------               intersection_right
Γ ⊢ τ₁ & τ₂ <: τ  


Γ ⊢ τ <: τ₁  
Γ ⊢ τ <: τ₂  
------------------                intersection
Γ ⊢ τ <: τ₁ & τ₂  



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