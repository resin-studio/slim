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
  τ ≤ τ                           operation
  C ∨ C                           disjunction
  C ∧ C                           conjunction

Δ ::=                             type context
  {..., α → τ, ...}
  Δ, Δ                        

m ::=                             renaming 
  {..., α → β, ...}
  m, m                        

o ::= some _ | none               option

Γ ::=                             term context
  {..., x → τ, ...}                        
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


`linearize_record τ = o`
```
linearize_record .l₁ τ₁ & .l₂ τ₂ =
  some (.l₁ τ₁ & .l₂ τ₂)
linearize_record .l τ₁ & τ₂ =
  some .l τ₁ & (linearize_record τ₂)
linearize_record τ₁ & .l τ₂ =
  some .l τ₂ & (linearize_record τ₁)
linearize_record τ₁ & τ₂ =
  none
```

`make_field_constraint Δ ⊢ τ * τ ≤ τ = o`
```
make_field_constraint Δ ⊢ τ₀ * .l τ₁ & τ₂ ≤ μ α . τ =
  let β₁ = fresh in
  let C₁ = τ₁ ≤ ∀ {β₁ → ?} ⟨(τ₀ & .l β₁ & τ₂) ≤ unroll (μ α . τ)⟩ . β₁ in
  C₁ ∧ make_field_constraint (Δ ⊢ τ₀ & .l τ₁ * τ₂ ≤ μ α . τ)

make_field_constraint Δ ⊢ τ₀ * .l τ₁ ≤ μ α . τ =
  let β₁ = fresh in
  let C₁ = τ₁ ≤ ∀ {β₁ → ?} ⟨(τ₀ & .l β₁) ≤ unroll (μ α . τ)⟩ . β₁ in
  C₁

make_field_constraint _ ⊢ _ * _ ≤ _ = none
```

-- TODO: add check for well-formed decreasing inductive type (μ α . τ)

`wf τ`
```
wf μ α . τ = well_founded α τ 
```

`well_induct α τ`
```
well_founded α  τ₁ | τ₂ = 
  wf (τ₁ | τ₂) andalso
  well_founded α τ₁ andalso
  well_founded α τ₂

well_founded α ∀ Δ ⟨C⟩ . τ = 
  α ∈ Δ orelse


```

`occurs α τ`
```
occurs α α = true
occurs α ? = false 
occurs α ⟨⟩ = false 
occurs α (#l τ) = occurs α τ 
occurs α (.l τ) = occurs α τ 
occurs α (τ₁ -> τ₂) = (occurs α τ₁) orelse (occurs α τ₂)
occurs α (τ₁ & τ₂) = (occurs α τ₁) orelse (occurs α τ₂)
occurs α (τ₁ | τ₂) = (occurs α τ₁) orelse (occurs α τ₂)
occurs α (∀ Δ ⟨C⟩ . τ) = 
  α ∉ Δ andalso
  (occurs α C) orelse (occurs α τ)
occurs α (μ β . t) = 
  α ≠ β andalso 
  (occurs α τ)
```

`occurs α C`
```
occurs α (τ' ≤ τ) = (occurs α τ') orelse (occurs α τ)
occurs α (C₁ ∨ C₂) = (occurs α C₁) orelse (occurs α C₂)
occurs α (C₁ ∧ C₂) = (occurs α C₁) orelse (occurs α C₂)
```

`subst Δ τ`
```
subst Δ α = Δ α 
subst Δ ? = ? 
subst Δ ⟨⟩ = ⟨⟩ 
subst Δ (#l τ) = #l (subst Δ τ) 
subst Δ (.l τ) = .l (subst Δ τ) 
subst Δ (τ₁ -> τ₂) = (subst Δ τ₁) -> (subst Δ τ₂)
subst Δ (τ₁ & τ₂) = (subst Δ τ₁) & (subst Δ τ₂)
subst Δ (τ₁ | τ₂) = (subst Δ τ₁) | (subst Δ τ₂)
subst Δ (∀ Δ' ⟨C⟩ . τ) = 
  let Δ = filter Δ ((α → _)  => α ∉ Δ') in
  (∀ Δ' ⟨subst Δ C⟩ . (subst Δ τ))
subst Δ (μ β . τ) = 
  let Δ = filter Δ ((α → _)  => α ≠ β) in
  subst Δ (μ β . τ)
```

`subst Δ C`
```
subst Δ (τ' ≤ τ) = (subst Δ τ') ≤ (subst Δ τ)
subst Δ (C₁ ∨ C₂) = (subst Δ C₁) ∨ (subst Δ C₂)
subst Δ (C₁ ∧ C₂) = (subst Δ C₁) ∧ (subst Δ C₂)
```

`rename m Δ`
```
rename m Δ = 
  fmap Δ (α → τ =>
    let β = m α in
    {β → subst m τ}
  )
```

`guard α τ`
```
guard α τ = 
  μ α . τ
  if occurs α τ else
  τ
```


`Δ α = τ` 
```
Δ α =  
  τ
  if {α → τ} ⊆ Δ else
  ?
```

`solve Δ ⊢ C = o`
```
solve Δ ⊢ C₁ ∧ C₂ =  
  fmap (solve Δ ⊢ C₁) (Δ' => 
    solve Δ, Δ' ⊢ C₂
  )
solve Δ ⊢ C₁ ∨ C₂ = 
  choose (solve Δ ⊢ C₁) (solve Δ ⊢ C₂)

solve Δ ⊢ (∀ Δ' ⟨C⟩ τ') ≤ τ =
  let rmap = fmap Δ (α → _ => {α → fresh}) in
  let Δ' = rename rmap Δ' in
  let C = subst rmap C in
  let τ' = subst rmap τ' in
  solve Δ, Δ' ⊢ C ∧ τ' ≤ τ 

solve Δ ⊢  τ' ≤ (∀ Δ' ⟨C⟩ τ) =
  let rmap = fmap Δ (α → _ => {α → fresh}) in
  let Δ' = rename rmap Δ' in
  let C = subst rmap C in
  let τ = subst rmap τ in
  solve Δ, Δ' ⊢ C ∧ τ ≤ τ' 

solve Δ ⊢ α ≤ τ =
  let τ' = Δ α in (
    let β = fresh in some {α → ((guard α τ) & β), β → ?}
    if τ' = ? else
    solve Δ ⊢ τ' ≤ τ
  )

solve Δ ⊢ τ' ≤ α =
  let τ = Δ α in (
    let β = fresh in some {α → ((guard α τ') | β), β → ?}  
    if τ = ? else
    (solve Δ ⊢ τ' ≤ τ)
  )

solve Δ ⊢ #l τ' ≤ μ α . τ =  
  solve Δ ⊢ #l τ' ≤ unroll (μ α . τ)  

solve Δ ⊢ μ α . τ' ≤ #l τ  =  
  solve Δ ⊢ unroll (μ α . τ') ≤ #l τ

solve Δ ⊢ .l τ' ≤ μ α . τ =  
  solve Δ ⊢ .l τ' ≤ unroll (μ α . τ)  

solve Δ ⊢ μ α . τ' ≤ .l τ  =  
  solve Δ ⊢ unroll (μ α . τ') ≤ .l τ


solve Δ ⊢ τ' ≤ μ α . τ =
  let true = ? ≤ ?
  fmap (linearze_record τ') (τ' =>
  fmap (make_field_constraint Δ ⊢ true * τ' ≤ μ α . τ) (C =>
    solve Δ ⊢ C 
  ))


solve Δ ⊢ μ α . τ' ≤ τ  =  
  solve_induct Δ ⊢ μ α . τ' ≤ τ

solve Δ ⊢ #l' τ' ≤ #l τ =
  solve Δ ⊢ τ' ≤ τ
  if l' = l else
  none

solve Δ ⊢ τ₁ | τ₂ ≤ τ =
  solve Δ ⊢ τ₁ ≤ τ ∧ τ₂ ≤ τ

solve Δ ⊢ τ ≤ τ₁ | τ₂ =
  solve Δ ⊢ τ ≤ τ₁ ∨ τ ≤ τ₂


solve Δ ⊢ τ ≤ τ₁ & τ₂ =
  solve Δ ⊢ τ ≤ τ₁ ∧ τ ≤ τ₂

solve Δ ⊢ τ₁ & τ₂ ≤ τ =
  solve Δ ⊢ τ₁ ≤ τ ∨ τ₂ ≤ τ


solve Δ ⊢ τ₁ -> τ₂' ≤ τ₁' -> τ₂ =
  solve Δ ⊢ τ₁' ≤ τ₁ ∧ τ₂' ≤ τ₂


solve τ ≤ τ = some {} 
solve _ = none 
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