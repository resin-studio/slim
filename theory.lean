-- a unityped language: checking, inference, and synthesis

-- syntax 
/-

x ∈ String                        term variable
l ∈ String                        label

cs ::=                            cases
  for t => t                      case singleton 
  cs for t => t                   cases extended 

fs ::=                            fields 
  .l t                            field singleton 
  fs .l t                         fields extended 

t ::=                             term
  _                               hole / irrelevant pattern
  x                               variable expression / pattern
  ()                              unit expression / pattern
  #l t                            variant expression / pattern
  fs                              record expression / pattern
  t.l                             record projection
  cs                              function expression
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
  {..., α ≤ τ, ...}
  Δ ∪ Δ                        

m ::=                             substitution 
  {..., α / τ, ...}
  m ∪ m                        

o[i] ::= some[i] | none           option

Γ ::=                             term context
  {..., x : τ, ...}                        
  Γ ∪ Γ                      

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
merge op Δ₁ Δ₂ =
  fmap Δ₁ (α → τ₁ =>
  fmap Δ₂ (β → τ₂ =>
    {α → τ₁ op (Δ₂ α), β → (Δ₁ β) op τ₂}
  ))
```

`merge o[Δ] o[Δ] = o[Δ]`
```
merge _ none none = none 
merge _ none o = o 
merge _ o none = o 
merge op (some Δ₁) (some Δ₂) = some (merge op Δ₁ Δ₂)
```


`linearize_record τ = o[fs]`
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

`make_field_constraint Δ ⊢ τ * τ ≤ τ = o[C]`
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
  fmap (keys τ₁) (ks₁ =>
  fmap (keys τ₂) (ks₂ =>
    some (ks₁ = ks₂)
  )) = Some true
  (keys τ₁) = (keys τ₂) 
```


`decreasing τ τ = b`
```
decreasing (#l τ) τ = true 
decreasing τ₁ τ₂ =  
  any τ₁ (.l τ => decreasing τ (project τ₂ l)) andalso
  all τ₁ (.l τ => ¬ increasing τ (project τ₂ l))
```

`increasing τ τ = b`
```
increasing τ₁ τ₂ = decreasing τ₂ τ₁
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

`solve Δ ⊢ C = o[Δ]`
```
solve Δ ⊢ C₁ ∧ C₂ =  
  merge & (solve Δ ⊢ C₁) (solve Δ ⊢ C₂)

solve Δ ⊢ C₁ ∨ C₂ = 
  merge | (solve Δ ⊢ C₁) (solve Δ ⊢ C₂)

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

solve Δ ⊢ (∀ Δ' ⟨C⟩ . τ') ≤ τ =
  -- quantified Δ' assumed to not be in Δ 
  map (solve Δ, Δ' ⊢ C ∧ τ' ≤ τ) (Δ'' =>
    some (map Δ' (α ≤ _ =>
      {α ≤ Δ''(α)}
    )) 
  )

solve Δ ⊢ τ' ≤ (∀ Δ' ⟨C⟩ . τ) =
  -- quantified Δ' assumed to not be in Δ 
  map (solve Δ, Δ' ⊢ C ∧ τ' ≤ τ) (Δ'' =>
    some (map Δ' (α ≤ _ =>
      {α ≤ Δ''(α)}
    )) 
  )

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
  map (linearze_record τ') (τ' =>
  map (make_field_constraint Δ ⊢ true * τ' ≤ μ α . τ) (C =>
    solve Δ ⊢ C 
  ))


solve Δ ⊢ μ α . τ' ≤ τ  =  
  solve_induct Δ ⊢ μ α . τ' ≤ τ

solve Δ ⊢ #l' τ' ≤ #l τ =
  solve Δ ⊢ τ' ≤ τ
  if l' = l else
  none

solve τ ≤ τ = some {} 
solve _ = none 
```

`patvars t = o[Γ]`
```
patvars x τ = 
  some {x : τ}
patvars (.l t₁) τ = 
  map (project τ l) (τ₁ =>
    patvars t₁ τ₁
  )
patvars (.l t fs) τ =
  map (patvars (.l t) τ) (Γ₁ =>
  map (patvars fs τ) (Γ₂ =>
    some (Γ₁ ∪ Γ₂)
  ))
...
```

`infer Γ Δ ⊢ t : τ = o[Δ;τ]`
```

infer Γ Δ ⊢ () : τ =
  map (solve Δ ⊢ C ∧ [] ≤ τ in) (Δ' =>
    some (Δ' , [])
  )

infer Γ Δ ⊢ x : τ = 
  let τ' = Γ x in
  let Δ', C, τ' = refresh τ' in
  map (solve Δ, Δ' ⊢ C ∧ τ' ≤ τ) (Δ' =>
    some (Δ' , τ')
  )

infer Γ Δ ⊢ (#l t₁) : τ =
  let α = fresh in
  map (solve Δ ⊢ (∀ {α} . (#l α)) ≤ τ) (Δ' => 
  map (infer Γ (Δ ∪ Δ') ⊢ t₁ : α) (Δ₁,τ₁ => 
    some (Δ' ∪ Δ₁ , #l τ₁)
  )

infer Γ Δ ⊢ (for t₁ : τ₁ => t₂) : τ =
  let Δ₁, τ₁ = τ₁[?/fresh] in
  let Γ₁ = patvars t₁ τ₁ in
  let β = fresh in
  map (solve Δ ⊢ (∀ Δ₁ ∪ {β} . τ₁ -> β) ≤ τ) (Δ' => 
  map (infer (Γ ∪ Γ₁) (Δ ∪ Δ') ⊢ t₂ : β) (Δ₂', τ₂' =>
    -- patvars (Γ₁) are NOT generalized in τ₂'
    some (Δ' ∪ Δ₂' , τ₁ -> τ₂')
  ))


infer Γ Δ ⊢ (for t₁ : τ₁ => t₂) cs : τ =
  map (infer Γ Δ ⊢ (for t₁ : τ₁ => t₂) : τ) (Δ', τ' =>
  map (infer Γ Δ ∪ Δ' ⊢ cs : τ₂) (Δ'', τ'' => 
    some (Δ' ∪ Δ'' , τ' & τ'')
  ))

infer Γ Δ ⊢ t t₁ : τ₂ =
  map (infer Γ Δ ⊢ t : ? -> τ₂ in) (Δ',τ' => 
  map (functify τ') (τ₁,τ₂' => 
  -- break type (possibly intersection) into premise and conclusion 
  map (infer Γ (Δ ∪ Δ') ⊢ t₁ : τ₁) (Δ₁',τ₁' =>
  map (solve Δ ∪ Δ' ∪ Δ₁' ⊢ τ' ≤ (τ₁' -> τ₂)) (Δ' =>
    some(Δ' , τ₂' & τ₂)
  ))))

infer Γ Δ ⊢ (.l t₁) : τ =
  let α = fresh in
  map (solve Δ ⊢ (∀ {α} . (.l α)) ≤ τ) (Δ' =>
  map (infer Γ (Δ ∪ Δ') ⊢ t₁ : α) (Δ₁ , τ₁ =>  
    some(Δ' ∪ Δ₁ , .l τ₁)
  ))

infer Γ Δ ⊢ (.l t₁) fs : τ =
  map (infer Γ Δ ⊢ (.l t₁) : τ) (Δ' , τ' =>
  map (infer Γ (Δ ∪ Δ') ⊢ fs : τ) (Δ'' , τ'' =>
    some(Δ' ∪ Δ'' , τ' & τ'')
  ))

infer Γ Δ ⊢ t.l : τ₂ =
  map (infer Γ Δ ⊢ t : (.l τ₂)) (Δ' , τ' =>
  map (project τ' l) (τ₂' => 
    some(Δ' , τ₂')
  ))

infer Γ Δ ⊢ fix t : τ =
  map (infer Γ Δ ⊢ t : (τ -> τ)) (Δ',τ' =>
  map (functify τ') (τ₁', τ₂' =>
    -- extract premise and conclusion 
    some(Δ' , τ₂')
  ))

infer Γ Δ ⊢ (let x : τ₁ = t₁ in t₂) : τ₂ =
  let Δ₁,τ₁ = τ₁[?/fresh] in
  map (infer Γ Δ ⊢ t₁ : (∀ Δ₁ . τ₁)) (Δ₁' , τ₁' => 
  map (infer (Γ ∪ {x → (∀ Δ₁' . τ₁')}) Δ ⊢ t₂ : τ₂) (Δ₂' , τ₂' =>
    -- τ₁' is generalized in τ₂'
    some(Δ₂' , τ₂')
  ))
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



/-
# examples 

## type flow
- how types flow between contexts

### inferred type
- infer type 
  - from form and context 
```
#zero()
-- infer _ _ ⊢ #zero() : _ = _, #zero[]
```

### propagated type
- propagate type
  - to solve type constraints locally 
```
(for n : nat =>
  let first = (for (x,y) : [str;?] => x) in
  first (n, _) 
  -- infer {n : nat} ⊢ first (n, _) : _ = none
    -- infer {n : nat} ⊢ (n,_) : [str;?]  = none
      -- solve _ ⊢ nat ≤ str = none
)
```

## type adaptation 
- how types adapt to changing contexts 

### narrowed type
- maintain leniency while increasing strictness
  - combine intersection (i.e. &) with unknown type (i.e. ?)
- lenient
  - maintain bottom actual type
  - τ & ? = τ & ⊥ = ⊥
- strict
  - narrow unknown expected type from known expected type
  - τ & ? = τ & ⊤ = τ 
```
(for i2n : int -> nat => 
(for s2n : str -> nat => 
  (for x : ? => (i2n x, s2n x))
  -- infer _ _ ⊢ (for x : ? => (i2n x, s2n x)) : _ = _ , int & str -> [nat;nat] 
    -- infer {x : α} {α ≤ ?} ⊢ (i2n x, s2n x) : _ = _ , nat;nat
    -- solve {α ≤ ?} ⊢ α ≤ int = {α ≤ int & ?}  
    -- solve {α ≤ int & ?} ⊢ α ≤ nat = {α ≤ int & str & ?}  
      -- solve {α ≤ int & β, β ≤ ?} ⊢ int & β ≤ str = {β ≤ str & ?}  
        -- solve {...} ⊢ int ≤ str ∨ β ≤ str = {β ≤ str & ?}  
          -- solve {...} ⊢ β ≤ str = {β ≤ str & ?}  

))
```

### widened type
- maintain leniency while increasing strictness
  - combine union (i.e. |) with unknown type (i.e. ?)
- leient
  - maintain top expected type 
  - τ | ? = τ | ⊤ = ⊤ 
- strict
  - widen unknown actual type from known actual type
  - τ | ? = τ | ⊥ = τ  
```
(pair : ∀ α . α -> α -> [α ; α] => 
(n : int => 
(s : str => 
  pair n s
  -- infer _ _ ⊢ (pair n s) = _ , [int|str ; int|str] 
    -- solve {α ≤ ?} ⊢ int ≤ α = some {α ≤ int | ?} 
    -- solve {α ≤ int | ?} ⊢ str ≤ α = some {α ≤ int | str | ?} 
      -- solve {α ≤ int | β, β ≤ ?} ⊢ str ≤ int | β  = {β ≤ str | ?} 
        -- solve {...} ⊢ str ≤ int ∨ str ≤ β = {β ≤ str | ?}
          -- solve {...} ⊢ str ≤ β = {β ≤ str | ?}
)))
```

-- TODO: check/tidy/extend the derivations below 

## type mapping
- how types map to types 

### record type

### function type
-- TODO: check that we can infer the type without infinite loop
```
fix (size => (
  -- size : α
  for #nil() => #zero()
  for #cons(_, xs) => #succ(size xs)
  -- solve ⊢ (α -> β) ≤ (#nil[] -> #zero[] & #cons[_;α] -> #succ[β])
))
-- infer ... ⊢ fix (size -> ...) = ∀ {α} . (#nil[] -> #zero[]) & (#cons[α;list[α]] -> #succ[nat])
...
```


## type induction
- how types are foundend on themselves

### scalar type
```
∀ {α} . μ list .  
  #nil[] | 
  #cons[α;list]
```
```
μ nat . 
  #zero[] | 
  #succ[nat]
```

### relational type 
```
∀ {α} . μ list_len .
  [#nil[] ; #zero[]] |
  ∀ {list,nat} [list;nat] ≤ list_len .  
    [#cons[α;list] ; #succ[nat]]
```


## type abstraction 
- how types choose an abstraction

### generalized type
```
(for (one, hello) : [nat;str] =>
let f = fn x => x in
-- Γ = {f : ∀ {α} . α -> α}

let one' = f one in 
-- Γ = {f : ∀ {α} . α -> α}, one' : (nat | ?)} 
  -- Γ = {f : ∀ {α} . α -> α}, one' : (∀ {α ≤ (nat | β), β ≤ ?} . α)} 
    -- infer {f : ∀ {α} . α -> α} ; {...} ⊢ f one : ? = ∀ {α ≤ (nat | β), β ≤ ?} . α    
      -- solve {α ≤ ?} ⊢ one ≤ α = {α ≤ nat | β, β ≤ ?}

let hello' = f hello in
-- same as above
...
)
```

### specialized type 
```
(for (one, hello) : [nat;str] =>
(fn f => 
  -- Γ = {f : α} ; Δ = {α ≤ ?}

  let one' = f one in
  -- infer {f : α} ; {α ≤ β₁ -> β₂, β₁ ≤ nat & β₃, β₃ ≤ ?} ⊢ f one : ? = ∀ {β₂ ≤ ?} . β₂    

  let hello' = f hello in
  -- infer {f : α} ; {α ≤ β₁ -> β₂, β₁ ≤ nat & str & β₃, β₃ ≤ ?} ⊢ f hello : ? = none
    -- solve {β₁ ≤ nat & str & β₃, β₃ ≤ ?} ⊢ str ≤ β₁ = none
      -- solve {...} ⊢ str ≤ nat & str = none
        -- solve {...} ⊢ str ≤ nat ∧ str ≤ str = none
          -- solve {...} ⊢ str ≤ nat = none
  ...
)(fn x => x)
)
```
-/