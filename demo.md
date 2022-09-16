consider:
```
let x = [1]
-- x : list[int]

let first : (list[str] ; ?) -> list[str]
let first = (a , b) => a 
-- first : (list[str] ; ?) -> list[str]

let _ = first (x, ... 
-- error: list[int] ≤ list[str]
```


basic typing: <br>
`Γ ⊢ t : τ` <br>

variable
```
(x : τ) ∈ Γ 
---------------------------                        
Γ ⊢ x : τ
```

application

```
Γ ⊢ t₁ : τ₁ -> τ₃ 
Γ ⊢ t₂ : τ₂
Γ ⊩ τ₂ ≤ τ₁
------------------------------- 
Γ ⊢ t₁ t₂ : τ₃
```


derivation: is `first (x, ...` well-typed?
```
Γ ⊢ first : (dict[str, ?] ; ?) -> dict[str, ?] 
Γ ⊢ (x, ... : ... 
Γ ⊩ ... ≤ (dict[str, ?] ; ?)
--------------------------------------------------
Γ ⊢ first (x, ... : ...
```


basic supertyping: <br>
`Γ ⊢ t : τ ≥ τ` <br>

variable
```
(x : τ₂) ∈ Γ 
Γ ⊩ τ₂ ≤ τ₁
---------------------------                        
Γ ⊢ x : τ₁ ≥ τ₂ 
```

application
```
Γ ⊢ t₁ : ? -> τ₁ ≥ τ₂ -> τ₃ 
Γ ⊢ t₂ : τ₂ ≥ _ 
------------------------------- 
Γ ⊢ t₁ t₂ : τ₁ ≥ τ₃
```


derivation: is `first (x, ...` well-typed?
```
(x : list[int]) ∈ Γ 
Γ ⊩ list[int] ≤ list[str]
-------------------------------
Γ ⊢ x : list[str] ≥ list[int]
```


consider:
```
let x = [] 
-- x : (∃ α ≤ ? . list[α])

let first : list[str] ; ? -> list[str] 
let first = (a , b) => a 
-- first : (list[str] ; ?) -> list[str]

let _ = first (x, x)  
-- ok 
```

polymorphic supertyping: <br> 
`Γ ⊢ t : τ ≥ τ` <br>

```
(x : ∀ Δ . τ₂) ∈ Γ 
Γ ⊩ (∃ Δ . τ₂) ≤ τ₁
---------------------------                        
Γ ⊢ x : τ₁ ≥ ∃ Δ . τ₂ 
```


derivation: is `first(x, x)` well-typed?
```
(x : ∀ α ≤ ? . list[α]) ∈ Γ 
Γ ⊩ (∃ α ≤ ? . list[α]) ≤ list[str]
--------------------------------------------------------------------
Γ ⊢ x : list[str] ≥ (∃ α ≤ ? . list[α])
```



consider:
```
let x = [] 
-- x : (∃ α ≤ ? . list[α])

let first : list[str] ; ? -> list[str] 
let first = (a , b) => a 
-- first : (list[str] ; ?) -> list[str]

let _ = first (x, x)  
-- ok 
-- treat first as a constraint on the type of x
-- strict option. x : list[str] 
-- lenient option. x : ∃ α . list[str | α]

let y = x ++ [4]
-- ++ : ∀ α ≤ ? . list[α] ; list[α] -> list[α]
-- strict option. error: list[int] ≤ list[str] 
-- lenient option. x : ∃ α . list[str | α]
```



supertyping + constraints: <br>
`Γ ; C ⊢ t : τ ≥ τ ; C` <br>
`Γ ; C ⊩ C`

variable
```
(x : ∀ Δ ⟨D⟩. τ₂) ∈ Γ 
Γ ; C ⊩ ∃ Δ ⟨D ∧ τ₂ ≤ τ₁⟩
-----------------------------------------------------             
Γ ; C ⊢ x : τ₁ ≥ ∃ Δ . τ₂ ; (∃ Δ ⟨D ∧ τ₂ ≤ τ₁⟩)
```
Note: cumbersome redunancy between supertyping and constraints
Note: type information may not be readable from constraints

supertyping * constraints, simple: <br>
`Γ ; C ⊢ t : τ ≥ τ` <br>
`Γ ; C ⊩ τ ≤ τ`

```
(x : ∀ Δ ⟨D⟩. τ₂) ∈ Γ 
Γ ; C ⊩ (∃ Δ ⟨D⟩ .τ₂) ≤ τ₁
-----------------------------------------------------             
Γ ; C ⊢ x : τ₁ ≥ ∃ Δ ⟨D ∧ τ₂ ≤ τ₁⟩ . τ₂
```
Note: cumbersome redunancy between supertyping and constraints
Note: type information may not be readable from constraints


supertyping * constraints, eager unification: <br>
`Γ ; C ⊢ t : τ ≥ τ` <br>
`Γ ; C ⊩ τ ≤ τ ~> Δ ; D`

```
(x : ∀ Δ ⟨D⟩. τ₂) ∈ Γ 
Γ ; C ⊩ (∃ Δ ⟨D⟩ .τ₂) ≤ τ₁ ~> Δ' ; D'
-----------------------------------------------------             
Γ ; C ⊢ x : τ₁ ≥ ∃ Δ' ⟨D'⟩ . τ₂
```
Note: type information readable in incomplete program 


derivation: strict option
```
(x : ∀ α ≤ ? . list[α]) ∈ Γ 
Γ ⊩ (∃ α ≤ ? . list[α]) ≤ list[str] ~> α ≤ str
--------------------------------------------------------------------
Γ ⊢ x : list[str] ≥ (∃ α ≤ str . list[α])
```


derivation: lenient option
```
(x : ∀ α ≤ ? . list[α]) ∈ Γ 
Γ ⊩ (∃ α ≤ ? . list[α]) ≤ list[str] ~> α ≤ (str | α)
--------------------------------------------------------------------
Γ ⊢ x : list[str] ≥ (∃ α ≤ (str | α) . list[α])
```