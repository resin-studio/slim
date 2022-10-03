-- a unityped language: checking, inference, and synthesis

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

`solve Δ ⊢ C = o`
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
  fmap (solve Δ, Δ' ⊢ C ∧ τ' ≤ τ) (Δ'' =>
    some (fmap Δ' (α ≤ _ =>
      {α ≤ Δ''(α)}
    )) 
  )

solve Δ ⊢ τ' ≤ (∀ Δ' ⟨C⟩ . τ) =
  -- quantified Δ' assumed to not be in Δ 
  fmap (solve Δ, Δ' ⊢ C ∧ τ' ≤ τ) (Δ'' =>
    some (fmap Δ' (α ≤ _ =>
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



solve τ ≤ τ = some {} 
solve _ = none 
```
`patvars t = Γ, Δ`
```
patvars x = 
  let α = fresh in
  {x : α}, {α ≤ ?} 
patvars .l t = patvars t
patvars .l t fs =
  let Γ₁, Δ₁ = (patvars t) in
  let Γ₂, Δ₂ = (patvars fs) in
  (Γ₁ ∪ Γ₂), (Δ₁ ∪ Δ₂) 
...
```

-- TODO: rewrite with separation of type env and type 
-- TODO: rewrite with options
`infer Γ ; Δ ⊢ t : τ = Δ, τ`
```

infer Γ ; Δ ⊢ () : τ =
  let Δ' = solve Δ ⊢ C ∧ [] ≤ τ in
  Δ' , []

infer Γ ; Δ ⊢ x : τ = 
  let τ' = Γ x 
  let Δ', C, τ' = refresh τ' in
  let Δ' = solve Δ, Δ' ⊢ C ∧ τ' ≤ τ in
  Δ' , τ'

infer Γ ; Δ ⊢ (#l t₁) : τ =
  let α = fresh in
  let Δ' = solve Δ ⊢ (∀ {α} . (#l α)) ≤ τ in
  let (∀ Δ₁ . τ₁) = infer Γ ; Δ ∪ Δ' ⊢ t₁ : α in
  (Δ' ∪ Δ₁) , (#l τ₁)

infer Γ ; Δ ⊢ (case t₁ : τ₁ => t₂) : τ =
  let Γ₀, Δ₀ = patvars t₁ in
  let Δ₁, τ₁ = τ₁[?/fresh]
  let Δ₁', τ₁' = infer Γ₀ ; Δ₀ ⊢ t₁ : (∀ Δ₁ . τ₁) in
  let β = fresh in
  let Δ' = solve Δ ⊢ (∀ Δ₁' ∪ {β} . τ₁' -> β) ≤ τ in
  let Δ₂', τ₂' = infer Γ ∪ Γ₁ ; Δ, Δ' ⊢ t₂ : β in
  -- patvars (Γ₁) are NOT generalized in τ₂'
  (Δ' ∪ Δ₂') , (τ₁' -> τ₂')


infer Γ ; Δ ⊢ (case t₁ : τ₁ => t₂) cs : τ =
  let Δ', τ' = infer Γ ; Δ ⊢ (case t₁ : τ₁ => t₂) : τ in
  let Δ'', τ'' = infer Γ ; Δ ∪ Δ' ⊢ cs : τ₂ in 
  (Δ' ∪ Δ'') , (τ' & τ'')

infer Γ ; Δ ⊢ t t₁ : τ₂ =
  let τ = ? -> τ₂ in
  let Δ' , τ' = infer Γ ; Δ ⊢ t : τ in
  let τ₁ -> τ₂' = inside_out τ' in 
  -- turn intersection inside out into function type
  let τ₁' = infer Γ ; Δ ∪ Δ' ⊢ t₁ : τ₁ in
  let Δ' = solve Δ ∪ Δ' ⊢ τ' ≤ (τ₁' -> τ₂) in
  Δ' , (τ₂' & τ₂)

infer Γ ; Δ ⊢ (.l t₁) : τ =
  let α = fresh in
  let Δ' = solve Δ ⊢ (∀ {α} . (.l α)) ≤ τ in
  let Δ₁ , τ₁ = infer Γ ; Δ ∪ Δ' ⊢ t₁ : α in
  (Δ' ∪ Δ₁) , (.l τ₁)

infer Γ ; Δ ⊢ (.l t₁) fs : τ =
  let Δ' , τ' = infer Γ ; Δ ⊢ (.l t₁) : τ in
  let Δ'' , τ'' = infer Γ ; Δ ∪ Δ' ⊢ fs : τ in
  (Δ' ∪ Δ'') , (τ' & τ'')

infer Γ ; Δ ⊢ t.l : τ₂ =
  let τ 
  let Δ' , τ' = infer Γ ; Δ ⊢ t : (.l τ₂) in
  let τ₂' = project τ' l in 
  Δ' , τ₂'

infer Γ ; Δ ⊢ fix t : τ =
  let Δ' , (τ' -> τ') = infer Γ ; Δ ⊢ t : (τ -> τ) in 
  Δ' . τ'

infer Γ ; Δ ⊢ (let x : τ₁ = t₁ in t₂) : τ₂ =
  let Δ₁ , τ₁ = τ₁[?/fresh]
  let Δ₁' , τ₁' = infer Γ ; Δ ⊢ t₁ : (∀ Δ₁ . τ₁) in
  let Δ₂' , τ₂' = infer Γ, {x → (∀ Δ₁' . τ₁')} ; Δ ⊢ t₂ : τ₂ in
  -- τ₁' is generalized in τ₂'
  Δ₂' , τ₂'

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
-- TODO: gather all examples from other doc

## actual type
what is the type of `x`?
-- NOTE: compare to lenient/strict for complete program
```
#zero()
-- infer ⊢ x : #zero() = _, #zero[]
```

## expected type
```
-- NOTE: compare to lenient/strict for incomplete program 
(case n : nat =>
(case (x,y) : [str;?] => 
  x 
) (n, _) 
)
-- infer {n : nat} ⊢ (... => ...)(n, _) = none
  -- solve _ ⊢ nat ≤ str = none
```

## sub variable type
```
-- TODO: check derivation
-- NOTE: compare to lenient/strict for type arg inference 
-- NOTE: narrow actual type, widen expected type
-- NOTE: int & ? as expected type, becomes int & ⊤ = int
(case i2s : int -> str => 
(case n2s : nat -> str => 
  (case x : ? => (i2s x, n2s x))
  -- infer {x : α} {α ≤ ?} ⊢ (... => ...) = _ , int & nat -> [str ; str] 
    -- solve {α ≤ ?} ⊢ α ≤ int = {α ≤ int & β, β ≤ ?}  
    -- solve {α ≤ int & β, β ≤ ?} ⊢ α ≤ nat = {α ≤ int & nat & ?}  
      -- solve {α ≤ int & β, β ≤ ?} ⊢ int & β ≤ nat = {β ≤ nat & ?}  
        -- solve {...} ⊢ int ≤ nat ∧ β ≤ nat = {β ≤ nat & ?}  

))
```

## super variable type
-- NOTE: widen expected type (input), narrow actual type (output)
-- NOTE: compare to lenient/strict for type param inference 
-- NOTE: ? is treated as ⊥ in sub/actual positions
-- NOTE: ? is treated as ⊤ in super/expected position
```
(pair : ∀ α . α -> α -> [α ; α] => 
(n : int => 
(s : str => 
  pair n s
  -- infer _ _ ⊢ (pair n s) = _ , [int|str ; int|str] 
    -- solve {α ≤ ?} ⊢ int ≤ α = some {α ≤ int | ?} 
    -- solve {α ≤ int | ?} ⊢ str ≤ α = some {α ≤ int | str | ?} 
      -- solve {α ≤ int | β, β ≤ ?} ⊢ str ≤ int | β  = {β ≤ str | ?} 
        -- solve {α ≤ int | β, β ≤ ?} ⊢ str ≤ int ∨ str ≤ β = {β ≤ str | ?}
          -- solve {α ≤ int | β, β ≤ ?} ⊢ str ≤ β = {β ≤ str | ?}
)))
```

`str | ? ≤ str` 

## record intersection type

## function intersection type
-- TODO: check that we can infer the type without infinite loop
```
fix (size => (
  -- size : α
  case #nil() => #zero()
  case #cons(_, xs) => #succ(size xs)
  -- solve ⊢ (α -> β) ≤ (#nil[] -> #zero[] & #cons[_;α] -> #succ[β])
))
-- infer ... ⊢ fix (size -> ...) = ∀ {α} . (#nil[] -> #zero[]) & (#cons[α;list[α]] -> #succ[nat])
...
```


## scalar inductive type
```
list a = μ list .  
  #nil[] | 
  #cons[a;list]
```

```
nat = μ nat . 
  #zero[] | 
  #succ[nat]
```

## relational inductive type 
```
list_len a = μ list_len .
    [#nil[] ; #zero[]] |
    ∀ {list,nat} [list;nat] ≤ list_len .  
      [#cons[a;list] ; #succ[nat]]
```


## polymorphic type
```
(case (one, hello) : [nat;str] =>
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


## monomorphic type 
```
(case (one, hello) : [nat;str] =>
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