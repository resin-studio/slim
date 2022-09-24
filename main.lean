-- surface syntax 
/-

x ∈ String                        term variable
l ∈ String                        label

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
  let t : τ = t in t              binding
  fix t                           recursion

-/

-- concrete canonical syntax 
/-
...
-/

-- abstract canonical syntax 
/-

α ∈ String                        type variable

τ ::=                             type
  α                               variable type
  ?                               unknown type
  ⟨⟩                              unit type
  #l τ                            variant type
  .l τ                            field type
  τ -> τ                          implication type 
  τ & τ                           intersection type
  τ | τ                           union type
  ∀ Δ ⟨C⟩ . τ                     universal schema 
  μ α . t                         inductive type

C ::=                             constraint
  τ ≤ τ                           subtyping
  C ∨ C                           disjunction
  C ∧ C                           conjunction

Δ ::=                             type context
  {}                              empty type context
  Δ{α → τ}                        type context extended with indentifier and its super type 

Γ ::=                             term context
  {}                              empty term context
  Γ{x → τ}                        term context extended with indentifier and its type 

-/

-- dynamic semantics 
/-
-/

-- static semantics 
/-
-/


-- dynamic implementation 
/-
beyond scope
-/

-- static implementation 
/-
-/


-- dynamic semantics/implementation theorems
/-
soundness: beyond scope 
completeness: beyond scope
-/

-- static/dynamic semantics theorems
/-
soundness: N/A
completeness: N/A
-/


-- static implementation/semantics theorems
/-
soundness: ...
completeness: ...
-/