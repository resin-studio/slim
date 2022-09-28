-- syntax 
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

α ∈ String                        type variable

τ ::=                             type
  α                               variable type
  ?                               unknown type
  []                              unit type
  #l τ                            variant type
  .l τ                            field type
  τ -> τ                          implication type 
  τ & τ                           intersection type
  τ | τ                           union type
  ∀ Δ C τ                         universal schema 
  μ α . τ                         inductive type
  [τ]                             grouped type

C ::=                             constraint
  .                               true
  ⟨C⟩                             grouped constraint 
  τ ≤ τ                           subtyping 
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

`Δ ⊢ C`
```
Δ ⊢ .

  Δ ⊢ C 
---
Δ ⊢ ⟨C⟩ 

  Δ ⊢ C₁ 
  Δ ⊢ C₂
---
Δ ⊢ C₁ ∧ C₂ 

  Δ ⊢ C₁ 
---
Δ ⊢ C₁ ∨ C₂ 

  Δ ⊢ C₂
---
Δ ⊢ C₁ ∨ C₂ 

Δ ⊢ τ ≤ τ

Δ ⊢ τ ≤ ? 

Δ ⊢ ? ≤ τ 

  Γ ⊢ τ' ≤ τₘ
  Γ ⊢ τₘ ≤ τ
  τₘ ≠ ?
---
Δ ⊢ τ' ≤ τ  


  {α → τ} ⊆ Δ
---
Δ ⊢ α ≤ τ  


  Δ₀, Δ' ⊢ C' ∧ τ' ≤ τ
---
Δ₀ ⊢ (∀ Δ' C' τ') ≤ τ


  Δ₀, Δ ⊢ C ∧ τ' ≤ τ
---
Δ₀ ⊢ τ' ≤ (∀ Δ C τ)


Δ₀ ⊢ (μ α . τ) ≤ unroll (μ α . τ)


Δ₀ ⊢ unroll (μ α . τ) ≤ (μ α . τ)


  Δ ⊢ τ₁' <: τ₁ 
  Δ ⊢ τ₂' <: τ₂ 
---
Δ ⊢ τ₁ -> τ₂' <: τ₁' -> τ₂


  Δ ⊢ τ' ≤ τ
---
Δ ⊢ .l τ' ≤ .l τ  


  Δ ⊢ τ' ≤ τ  
---
Δ ⊢ #l τ' ≤ #l τ


Δ ⊢ τ' ≤ (τ' | τ)  

Δ ⊢ τ' ≤ (τ | τ')  


  Δ ⊢ τ₁ ≤ τ   
  Δ ⊢ τ₂ ≤ τ  
---
Δ ⊢ (τ₁ | τ₂) ≤ τ 


Δ ⊢ (τ & τ') ≤ τ

Δ ⊢ (τ' & τ) ≤ τ  


  Δ ⊢ τ' ≤ τ₁  
  Δ ⊢ τ' ≤ τ₂  
---
Δ ⊢ τ' ≤ τ₁ & τ₂  
```

`Γ ; Δ ; C ⊢ t : τ`
```
---
Γ ; Δ ; C ⊢ t : τ
```

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

`fields τ = o`
```
fields τ₁ & τ₂ = 
  fmap (fields τ₁) (s₁ =>
  fmap (fields τ₂) (s₂ =>
    s₁ ∪ s₂
  )) 
fields (.l τ) =
  some {l → τ}
fields _ =
  none 
```

`keys τ = o`
```
keys τ =
  map (fields τ) (fs =>
    fmap fs (l → τ => {l})
  )
```

`match o o = b`
```
match (some x₁) (some ×₂) = 
  x₁ = x₂
match none _ = false
match _ none = false
```

`cases_normal τ τ = b`
```
cases_normal (#l₁ τ₁) (#l₂ τ₂) = true
cases_normal τ₁ τ₂ = 
  match (keys τ₁) (keys τ₂) 
```


`decreasing τ τ = b`
```
decreasing (#l τ) τ = true 
decreasing τ₁ τ₂ = 
  decreasing (fields τ₁) (fields τ₁)
```

`increasing τ τ = b`
```
increasing τ₁ τ₂ = decreasing τ₂ τ₁
```

`decreasing o o = b`
```
decreasing (some fs₁) (some fs₂) =  
  any fs₁ (α → τ => decreasing τ (fs₂ α)) andalso
  all fs₁ (α → τ => ¬ increasing τ (fs₂ α))
decreasing none _ = false
decreasing _ none = false
```

`well_founded α τ = b`
```
well_founded α τ₁ | τ₂ = 
  cases_normal τ₁ τ₂ andalso
  well_founded α τ₁ andalso
  well_founded α τ₂

well_founded α ∀ Δ ⟨τ' ≤ α⟩ . τ = 
  α ∈ Δ orelse
  decreasing τ τ' 
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
subst Δ [] = [] 
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

`unroll μ α . τ = τ`
```
unroll μ α . τ = subst {α → μ α . τ} τ
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

`refresh τ = Δ, C, τ`
```
refresh (∀ Δ ⟨C⟩ τ) =
  let rmap = fmap Δ (α → _ => {α → fresh}) in
  let Δ = rename rmap Δ in
  let C = subst rmap C in
  let τ = subst rmap τ in
  Δ, C, τ 

refresh τ = 
  {}, ? ≤ ?, τ
```

`solve Δ ⊢ C = o`
```
solve Δ ⊢ C₁ ∧ C₂ =  
  fmap (solve Δ ⊢ C₁) (Δ' => 
  fmap (solve Δ, Δ' ⊢ C₂) (Δ'' =>
    some Δ', Δ''
  ))
solve Δ ⊢ C₁ ∨ C₂ = 
  choose (solve Δ ⊢ C₁) (solve Δ ⊢ C₂)

solve Δ ⊢ (∀ Δ' ⟨C⟩ . τ') ≤ τ =
  let rmap = fmap Δ (α → _ => {α → fresh}) in
  let Δ', C, τ' = refresh (∀ Δ' ⟨C⟩ . τ') in
  solve Δ, Δ' ⊢ C ∧ τ' ≤ τ 

solve Δ ⊢ τ' ≤ (∀ Δ' ⟨C⟩ . τ) =
  let rmap = fmap Δ (α → _ => {α → fresh}) in
  let Δ', C, τ = refresh (∀ Δ' ⟨C⟩ . τ) in
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

`infer Γ ; Δ ⊢ t : τ = τ`
```

infer Γ ; Δ ⊢ () : τ =
  let Δ' = solve Δ ⊢ C ∧ [] ≤ τ in
  (∀ Δ' . [])

infer Γ ; Δ ⊢ (#l t) : τ =
  let (∀ Δ₁ ⟨⟩ τ₁) = infer Γ ; Δ ⊢ t : ? in
  let Δ' = solve Δ ⊢ (∀ Δ₁ . (#l τ₁)) ≤ τ in
  (∀ Δ' . (#l τ₁))

infer Γ ; Δ ⊢ (.l t) : τ =
  let (∀ Δ₁ . τ₁) = infer Γ ; Δ ⊢ t : ? in
  let Δ' = solve Δ ⊢ (∀ Δ₁ . (.l τ₁)) ≤ τ in
  (∀ Δ' . (.l τ₁))

infer Γ ; Δ ⊢ (.l t) fs : τ =
  let (∀ Δ₁ . τ₁) = infer Γ ; Δ ⊢ t : ? in
  let (∀ Δ₂ . τ₂) = infer Γ ; Δ ⊢ fs : ? in
  let Δ' = solve Δ ⊢ (∀ Δ₁, Δ₂ . (.l τ₁) & τ₂) ≤ τ in
  (∀ Δ' . (.l τ₁) & τ₂)

infer Γ ; Δ ⊢ t.l : τ =
  let τ' = infer Γ ; Δ ⊢ t : (.l τ) in
  τ'


infer Γ ; Δ ⊢ (match t₁' case t₁ => t₂) : τ₂ =
  let τ₁' = infer Γ ; Δ ⊢ t₁ : ? in
  let (∀ Δ' . _) = infer Γ ; Δ  ⊢ t₁' : τ₁' in
  let τ₂' = infer Γ ; Δ, Δ' ⊢ t₂ : τ₂ in
  τ₂'

infer Γ ; Δ ⊢ (match t₁' case t₁ => t₂ cs) : τ₂ =
  let τ₂' = infer Γ ; Δ ⊢ (match t₁' case t₁ => t₂) : τ₂ in
  let τ₂'' = infer Γ ; Δ ⊢ (match t₁' cs) : τ₂ in
  τ₂' | τ₂''


infer Γ ; Δ ⊢ fix t : τ =
  let (∀ Δ' . τ' -> τ') = infer Γ ; Δ ⊢ t : (τ -> τ) in 
  (∀ Δ' . τ')


infer Γ ; Δ ⊢ x : τ = 
  let τ' = Γ x 
  let Δ', C, τ' = refresh τ' in
  let Δ' = solve Δ, Δ' ⊢ C ∧ τ' ≤ τ in
  (∀ Δ' . τ')

infer Γ ; Δ ⊢ (let x : τ₁ = t₁ in t₂) : τ₂ =
  let Δ₁, τ₁ = τ₁[?/fresh]
  let τ₁' = infer Γ ; Δ ⊢ t₁ : (∀ Δ₁ . τ₁) in
  let τ₂' = infer Γ, {x → τ₁'} ; Δ ⊢ t₂ : τ₂ in
  τ₂'

infer Γ ; Δ ⊢ (x : τ₁ => t) : (τ₁' -> τ₂) =
  let Δ₁, τ₁ = τ₁[?/fresh] in
  let τ₂' = infer Γ, {x → τ₁} ; Δ, Δ₁ ⊢ t : τ₂ in
  (∀ Δ₁ . τ₁ -> τ₂')

infer Γ ; Δ ⊢ t₁ t₂ : τ₁ =
  let ∀ Δ' . τ₂ -> τ₁' = infer Γ ; Δ ⊢ t₁ : ? -> τ₁ in
  let τ₂' = infer Γ ; Δ, Δ' ⊢ t₂ : τ₂ in
  let Δ' = solve Δ, Δ' ⊢ τ₂' ≤ τ₂ ∧ τ₁' ≤ τ₁ in
  (∀ Δ' . τ₁')


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