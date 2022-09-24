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
  {α → τ}
  Δ, Δ                        

o ::= some Δ | none               optional type context

Γ ::=                             term context
  {x → τ}                        
  Γ, Γ                      

-/

-- dynamic semantics 
/-
-/

-- dynamic implementation 
/-
beyond scope
-/

-- dynamic semantics/implementation theorems
/-
beyond scope
-/

-- static semantics 
/-
-/

-- static implementation 
/-


`merge Δ Δ = Δ`
```
merge Δ₁ Δ₂ =
  fmap Δ₁ (α → τ₁ =>
  fmap Δ₂ (β → τ₂ =>
    {α → τ₁ | (Δ₂ α), β → (Δ₁ β) | τ₂}
  ))
```

`choose o o = o`
```
choose none none = none 
choose none o = o 
choose o none = o 
choose (some Δ₁) (some Δ₂) = some (merge Δ₁ Δ₂)
```

`solve Δ ⊢ C = o`
```
solve Δ ⊢ C₁ ∧ C₂ =  
  fmap (solve Δ ⊢ C₁) (Δ' => 
    solve Δ, Δ' ⊢ C₂
  )
solve Δ ⊢ C₁ ∨ C₂ = 
  choose (solve Δ ⊢ C₁) (solve Δ ⊢ C₂)

solve Δ ⊢ τ₁ | τ₂ ≤ τ =
  solve Δ ⊢ τ₁ ≤ τ ∧ τ₂ ≤ τ

solve Δ ⊢ τ ≤ τ₁ | τ₂ =
  Δ ⊢ τ ≤ τ₁ ∨ τ ≤ τ₂
```


intersection_left
Γ ⊩ τ₁ ≤ τ ∨ τ₂ ≤ τ ~> Δ
----------------------------------
Γ ⊩ τ₁ & τ₂ ≤ τ ~> Δ 

intersection_right
Γ ⊩ τ ≤ τ₁ ∧ τ ≤ τ₂ ~> Δ 
----------------------------------
Γ ⊩ τ ≤ τ₁ & τ₂ ~> Δ

exists_left
Δ # Γ
Γ, Δ ⊩ D ∧ τ' ≤ τ ~> Δ' 
-----------------------------------
Γ ⊩ ∃ Δ ⟨D⟩ τ' ≤ τ ~> Δ' 

exists_right
Δ # Γ
Γ, Δ ⊩ D ∧ τ' ≤ τ ~> Δ' 
-----------------------------------
Γ ⊩ τ' ≤ ∃ Δ ⟨D⟩ τ ~> Δ' 


variable_left_write
{α → ?} ⊆ Γ
β # (Γ, τ)
----------------------------------
Γ ⊩ α ≤ τ ~> {α → (τ & β), β → ?}  

variable_left_read
{α → τ'} ⊆ Γ
Γ ⊩ τ' ≤ τ ~> Δ 
------------------------------------
Γ ⊩ α ≤ τ ~> Δ 


variable_right_write
{α → ?} ⊆ Γ    
β # (Γ, τ)
----------------------------------
Γ ⊩ τ ≤ α ~> {α → (τ | β), β → ?}  

variable_right_read
```
{α → τ} ⊆ Γ
Γ ⊩ τ' ≤ τ ~> Δ  
----------------------------------
Γ ⊩ τ' ≤ α ~> Δ 
```


-/

-- static implementation/semantics theorems
/-
soundness: ...
completeness: ...
-/


-- static/dynamic semantics theorems
/-
soundness: N/A
completeness: N/A
-/