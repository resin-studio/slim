-- examples 
/-
## type flow
- how types move between contexts

### inferred type
- infer type from form and context 
```
#zero()

-- infer _ _ ⊢ #zero() : _ = some _, #zero[]
```

### propagated type
- propagate type to solve type constraints locally 
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
- how types adjust to changing contexts 

### narrowed type
```
(for i2n : int -> nat => 
(for s2n : str -> nat => 
  (for x : ? => (i2n x, s2n x))

  -- infer _ _ ⊢ (for x : ? => (i2n x, s2n x)) : _ = some _ , int & str -> [nat;nat] 
    -- infer {x : α} {α ≤ ?} ⊢ (i2n x, s2n x) : _ = some _ , nat;nat
    -- solve {α ≤ ?} ⊢ α ≤ int = some {α ≤ int & ?}  
    -- solve {α ≤ int & ?} ⊢ α ≤ str = some {α ≤ int & str & ?}  
      -- solve {α ≤ int & β, β ≤ ?} ⊢ int & β ≤ str = some {β ≤ str & ?}  
        -- solve {...} ⊢ int ≤ str ∨ β ≤ str = some {β ≤ str & ?}  
          -- solve {...} ⊢ β ≤ str = some {β ≤ str & ?}  

))
```
- maintain leniency while increasing strictness
  - combine intersection (i.e. &) with unknown type (i.e. ?)
- lenient
  - maintain bottom actual type
  - τ & ? = τ & ⊥ = ⊥
- strict
  - narrow unknown expected type from known expected type
  - τ & ? = τ & ⊤ = τ 


### widened type
```
(pair : ∀ α . α -> α -> [α ; α] => 
(n : int => 
(s : str => 
  pair n s

  -- infer _ _ ⊢ (pair n s) = _ , [int|str ; int|str] 
    -- solve {α ≤ ?} ⊢ int ≤ α = some {α ≤ int | ?} 
    -- solve {α ≤ int | ?} ⊢ str ≤ α = some {α ≤ int | str | ?} 
      -- solve {α ≤ int | β, β ≤ ?} ⊢ str ≤ int | β  = some {β ≤ str | ?} 
        -- solve {...} ⊢ str ≤ int ∨ str ≤ β = some {β ≤ str | ?}
          -- solve {...} ⊢ str ≤ β = some {β ≤ str | ?}
)))
```
- maintain leniency while increasing strictness
  - combine union (i.e. |) with unknown type (i.e. ?)
- lenient
  - maintain top expected type 
  - τ | ? = τ | ⊤ = ⊤ 
- strict
  - widen unknown actual type from known actual type
  - τ | ? = τ | ⊥ = τ  

## type expression 
- how types index into types 

### record type
```
let pair = (for x, y =>
  .left x .right y

  -- infer {x : α, y : β} _ ⊢ (.left x .right y) : _ = some _ , (.left α) & (.right β)
)
```

### function type
```
fix (size =>
  for #nil() => #zero()
  for #cons(_, xs) => #succ(size xs)

  -- infer {size : α -> β} _ ⊢ (for ... for ...) : α = some _ , (#nil[] -> #zero[]) & (#cons[_;α] -> #succ[β])
)
```


### variants induction type
```
μ list .  
  #nil[] | 
  ∃ α . #cons[α;list]
```
```
μ nat . 
  #zero[] | 
  #succ[nat]
```

### relational induction type 
```
μ list_len .
  [#nil[] ; #zero[]] |
  ∃ {list,nat} [list;nat] ≤ list_len
    [#cons[α;list] ; #succ[nat]]
```


```
μ nat_list .
  [#zero[] ; #nil[]] |
  ∃ {nat,list} [nat;list] ≤ nat_list .
    [#succ[nat] ; #cons[α;list]]
```

-- equivalent to the notion
```
  [#nil[] ; #zero[]] ≤ list_len ∧

  ∀ list;nat ,
    ([list;nat] ≤ list_len --> [#cons[α;list] ; #succ[nat]] ≤ list_len)
```

-- related to the sigma type from dependent type theory
```
type dlist (n ≤ nat) := list for n;list ≤ nat_list 

(Σ n ≤ nat . dlist n) ≡ nat_list 

(Σ n ≤ nat . list for n;list ≤ nat_list . list) ≡ nat_list 
```


### function induction type 

```
μ list_to_len .
  [#nil[] -> #zero[]] & 
  ∀ {list,nat} [list -> nat] ≤ list_to_len .  
    [#cons[α;list] -> #succ[nat]]
```

```
μ nat_to_list .
  [#nil[] -> #zero[]] & 
  ∀ {nat,list} [nat -> list] ≤ nat_to_list .  
    [#succ[nat] -> #cons[α;list]]
```


## type range
- how types may be used over various terms 

### generalized type
```
(for one : nat =>
(for hello : str =>

let f = for x => x in

let one' = f one in 

-- infer {f : ∀ {α} . α -> α} _ ⊢ (f one) : _ = some _ , nat 

let hello' = f hello in

-- infer {f : ∀ {α} . α -> α} _ ⊢ (f hello) : _ = some _ , str 
)
```

### specialized type 
```
(for one : nat =>
(for hello : str =>

(for f => 
  let one' = f one in

  -- infer {f : α} _ ⊢ (f one) = some {α ≤ nat -> ?} , _

  let hello' = f hello in

  -- infer {f : α} _ ⊢ (f hello) = none 

  ...
)(for x => x)
))
```
-/

-- background
/-

- a unityped language allows all terms to belong to the same type, known as top (i.e. ⊤)

- a subtyping language enables terms to be reused across different levels of restriction
- no terms belong to the most restrictive type, known as bottom (i.e. ⊥)

- a term may be used at a position:
  - if the term's actual type is a subtype of the position's expected type
  - if the position's expected type is a supertype of the term's actual type

- types may be widened by the union operator (i.e. |).
  - widening an expected type increases leniency
  - widening an actual type increases strictness

- types may be narrowed by the intersection operator (i.e. &)
  - narrowing an expected type increases strictness
  - narrowing an actual type increases leniency 

- the unknown type (i.e. ?) has special consistent subtyping semantics
  - behaves like a bottom type for actual types
  - behaves like a top type for expected types

- the singleton type (e.g. #l []) corresponds to a single literal term
-/

-- innovations 
/-
- inference of types while balancing strictness and leniency
- synthesis of terms from context, examples, and types 
-/

-- related languages 
/-
- python
- typescript
-/

-- related techniques 
/-
- consistent subtyping (Siek)
- roundtrip typing (Polikarpova)
- type inference (Hindley/Milner)
- let-polymorphism (Damas)
- synthesis from examples as types (Walker)
-/


-- conventions 
/-
- forward style rules place premises above conclusions 
- backward style rules place premises below conclusions
- premises are indented relative to conclusions
- declarative rules are written as predicates in forward style
- procedural rules are written as functions in backward style
- derivations are written as propositions in backward style
-/


-- tasks
/-
- [x] learn PHOAS for pattern matching
- [x] learn macros in Lean 
- [_] learn termination for PHOAS in Lean 
  - difficulty due to mutual inductive defs and Sigma
- [_] determine how to represent bound variables 
  - locally nameless de bruijn
- [_] determine how to represent free variables
  - free var natural number
    - natural number = 1 + max(prev natural numbers)
    - assoc list of (free var, type) independent of term
  - dependent phoas / de bruijn: all variables are free with a local context

- consider adding relative complement type 
  - i.e. binary negation type operator
  - i.e. (τ₁ \ τ₂) ≤ (τ₁ & ¬ τ₂), where ⊤ / τ₂ = ¬ τ₂)
- write paper
  - type-directed synthesis for dynamic languages
  - explain static unitype view of dynamic types
  - state of the art
  - weaknesses of state of the art
  - refinement types vs unityped subtyping
  - solution
  - evidence
-/

-- syntax 
/-
α ∈ terminal                      type variable
l ∈ terminal                      label

Δ ::=                             subtyping environment 
  ⬝                                empty
  Δ ; α ≤ τ                       extension

τ ::=                             type
  ?                               unknown
  α                               variable
  *                               unit
  #l τ                            variant
  .l τ                            field
  τ ∪ τ                           union
  τ ∩ τ                           intersection
  τ -> τ                          func 
  ∀ Δ C τ                         universal schema 
  ∃ Δ C τ                         existential schema 
  μ α . τ                         induction

C ::=                             constraint
  .                               true
  τ ≤ τ                           subtyping 
  C ∨ C                           disjunction
  C ∧ C                           conjunction

-/

mutual 
  inductive Ty : Type
    | unknown : Ty
    | bvar : Nat -> Ty  
    | fvar : Nat -> Ty
    | unit : Ty
    | variant : String -> Ty -> Ty
    | field : String -> Ty -> Ty
    | union : Ty -> Ty -> Ty
    | inter : Ty -> Ty -> Ty
    | func : Ty -> Ty -> Ty
    | univ : List Ty -> Constr -> Ty -> Ty
    | induct : Ty -> Ty

  inductive Constr : Type
    | tru : Constr
    | subtype : Ty -> Ty -> Constr
    | disj : Constr -> Constr -> Constr
    | conj : Constr -> Constr -> Constr
end


declare_syntax_cat slm
syntax num : slm 
syntax ident : slm
syntax "[" slm,+ "]" : slm 
syntax "£"slm:90 : slm
syntax "@"slm:90 : slm
syntax "◇" : slm
syntax "#"slm:90 slm : slm
syntax "."slm:90 slm : slm
syntax "(_)" : slm
syntax "(=)" : slm
syntax "?" : slm
syntax:50 slm:50 "->" slm:51 : slm
syntax:60 slm:60 "∪" slm:61 : slm
syntax:70 slm:70 "∩" slm:71 : slm
syntax "∀" slm slm "." slm : slm 
syntax "∀" slm "." slm : slm 
syntax "μ 0 ." slm : slm 

syntax:30 slm:30 "∨" slm:31 : slm
syntax:40 slm:40 "∧" slm:41 : slm
syntax:50 slm:50 "≤" slm:51 : slm

syntax "(" slm ")" : slm

syntax "⟨" term "⟩" : slm 

syntax "[: " slm ":]" : term

macro_rules

-- terminals
  | `([: $n:num :]) => `($n)
  | `([: $a:ident:]) => `($(Lean.quote (toString a.getId)))
-- context 
  | `([: [$x:slm] :]) => `([ [: $x :] ])
  | `([: [$x,$xs:slm,*] :]) => `([: $x :] :: [: [$xs,*] :])
-- Ty 
  | `([: £$n :]) => `(Ty.bvar [: $n :])
  | `([: @$n:slm :]) => `(Ty.fvar [: $n :])
  | `([: ◇ :]) => `(Ty.unit)
  | `([: #$a $b:slm :]) => `(Ty.variant [: $a :] [: $b :])
  | `([: .$a $b:slm :]) => `(Ty.field [: $a :] [: $b :])
  | `([: ? :]) => `(Ty.unknown)
  | `([: $a -> $b :]) => `(Ty.func [: $a :] [: $b :])
  | `([: $a ∪ $b :]) => `(Ty.union [: $a :] [: $b :])
  | `([: $a ∩ $b :]) => `(Ty.inter [: $a :] [: $b :])
  | `([: ∀ $a:slm $b:slm . $c:slm :]) => `(Ty.univ [: $a :] [: $b :] [: $c :])
  | `([: ∀ $a:slm . $b:slm :]) => `(Ty.univ [: $a :] [: (=) :] [: $b :] )
  | `([: μ 0 . $a :]) => `(Ty.induct [: $a :])
-- Constr
  | `([: (=) :]) => `(Constr.tru)
  | `([: $a:slm ≤ $b:slm :]) => `(Constr.subtype [: $a :] [: $b :])
  | `([: $a ∨ $b :]) => `(Constr.disj [: $a :] [: $b :])
  | `([: $a ∧ $b :]) => `(Constr.conj [: $a :] [: $b :])

-- generic
  | `([: ($a) :]) => `([: $a :])

--escape 
  | `([: ⟨ $e ⟩ :]) => pure e


-- #check [: @⟨1⟩ :]


def z := 1
#check [: @⟨z⟩ :]
def x := Ty.bvar 1

-- #check [: ~foo ? ∪ ~boo ? :]
-- #check [: #foo ? ∪ #boo ? :]
-- #check [: #foo ◇ ∪ #boo ◇ :]
-- #check [: #foo * ∪ #boo * :]


#check [: £0 ∩ ? :]
#check [: ∀ [?] (=) . ⟨x⟩ :]
#check [: ∀ [?] (=) . £0 :]
#check [: ∀ [?, ?] (=) . £0 :]
#check [: ∀ [?, ?] . £0 :]
#check [: ◇ :]
#check [: @24 :]
#check [: #foo ◇ ∪ #boo ◇ :]
#check [: μ 0 . #foo £0 :]
#check [: μ 0 . #foo £0  ∩ ? ∪ @2 ∩ ?:]
#check [: £3 ∩ ? -> @1 ∪ @2 :]
#check [: μ 0 . #foo £0  ∩ ? ∪ @2 ∩ ? -> @1 ∪ @2 :]
#check [: μ 0 . #foo £0  ∩ ? ∪ @2 ∩ ? :]
#check [: ? :]
#check [: (=) ∧ (=) :]
#check [: ? ≤ ? ∩ £0 ∧ (=) :]

mutual 
  inductive Ty.has_size : Ty -> Nat -> Type
    | unknown : Ty.has_size Ty.unknown 0 
    | bvar : Ty.has_size (Ty.bvar _) 0 
    | fvar : Ty.has_size (Ty.fvar _) 0 
    | unit : Ty.has_size (Ty.unit) 0 
    | variant : Ty.has_size ty n -> Ty.has_size (Ty.variant _ ty) (n + 1) 
    | field : Ty.has_size ty n -> Ty.has_size (Ty.field _ ty) (n + 1) 
    | union : Ty.has_size ty₁ n₁ -> Ty.has_size ty₂ n₂ -> Ty.has_size (.union ty₁ ty₂) (n₁ + n₂ + 1)
    | inter : Ty.has_size ty₁ n₁ -> Ty.has_size ty₂ n₂ -> Ty.has_size (.inter ty₁ ty₂) (n₁ + n₂ + 1)
    | func : Ty.has_size ty₁ n₁ -> Ty.has_size ty₂ n₂ -> Ty.has_size (.func ty₁ ty₂) (n₁ + n₂ + 1)
    | univ : ListTy.has_size ctx ns -> Constr.has_size c n_ty -> Ty.has_size ty n_ty -> 
        Ty.has_size (Ty.univ ctx c ty) (ns + n_c + n_ty + 1)
    | induct : Ty.has_size ty n -> Ty.has_size (Ty.induct ty) (n + 1) 

  inductive ListTy.has_size : (List Ty) -> Nat -> Type
    | nil : 
        ListTy.has_size [] 0
    | cons : 
        Ty.has_size ty n_ty -> 
        ListTy.has_size tys n_tys -> 
        ListTy.has_size (ty::tys) (n_tys + n_ty)

  inductive Constr.has_size : Constr -> Nat -> Type
    | tru : 
        Constr.has_size Constr.tru 0  
    | subtype : 
        Ty.has_size ty₁ n₁ -> Ty.has_size ty₂ n₂ -> 
        Constr.has_size (Constr.subtype ty₁ ty₂) (n₁ + n₂ + 1) 
    | disj :
        Constr.has_size c₁ n₁ -> Constr.has_size c₂ n₂ -> 
        Constr.has_size (Constr.disj ty₁ ty₂) (n₁ + n₂ + 1) 
    | conj :
        Constr.has_size c₁ n₁ -> Constr.has_size c₂ n₂ -> 
        Constr.has_size (Constr.disj ty₁ ty₂) (n₁ + n₂ + 1) 
end


#check Nat.lt

@[reducible] def Ty.lt (ty₁ : Ty) (ty₂ : Ty) : Prop := 
  ∀ n₁ n₂ , Ty.has_size ty₁ n₁ -> Ty.has_size ty₂ n₂ -> n₁ < n₂

example : ¬ Ty.lt Ty.unknown Ty.unknown := 
  ((fun h =>
    let f := h 0 0 
    let w := f Ty.has_size.unknown Ty.has_size.unknown
    let z := Nat.ne_of_lt w
    absurd rfl z
  ))

example : ¬ Ty.lt Ty.unknown Ty.unknown := by
  unfold Ty.lt
  intro h 
  generalize (h 0 0) = f 
  generalize (f Ty.has_size.unknown Ty.has_size.unknown) = w 
  generalize Nat.ne_of_lt w = z
  apply absurd (rfl) z 

-- def Ty.acc : (a : Ty) -> Acc lt a

-- theorem Ty.wf : WellFounded Ty.lt := 
--   (WellFounded.intro (fun 
--     | Ty.unknwon => Acc.intro 
--   ))



def Constr.lt (c₁ : Constr) (c₂ : Constr) : Prop := 
  ∀ n₁ n₂ , Constr.has_size c₁ n₁ -> Constr.has_size c₂ n₂ -> n₁ < n₂

#check Sum
#check ((Sum.inl 1)) 

def TyConstr.lt (p₁ : (Sum Ty Constr)) (p₂ : Sum Ty Constr) : Prop :=
  match (p₁, p₂) with
    | (Sum.inl ty₁, Sum.inl ty₂) =>  Ty.lt ty₁ ty₂
    | (.inl ty₁, .inr c₂)  =>
        ∀ n₁ n₂ , Ty.has_size ty₁ n₁ -> Constr.has_size c₂ n₂ -> n₁ < n₂
    | (.inr c₁, .inl ty₂) =>
        ∀ n₁ n₂ , Constr.has_size c₁ n₁ -> Ty.has_size ty₂ n₂ -> n₁ < n₂
    | (.inr c₁, .inr c₂) => Constr.lt c₁ c₂ 


-- instance : WellFoundedRelation (Sum Ty Constr) where
--   rel := TyConstr.lt 
--   wf :=  


/-
x ∈ terminal                      term variable

p ::=                             term
  _                               hole
  x                               variable
  ()                              unit
  #l p                            variant
  ps                              record

ps ::=                            fields 
  .l p                            field singleton 
  ps .l p                         fields extended 
-/


mutual
  inductive Pat : (T : Type) -> Nat -> Type where
    | hole : Pat T 0 
    | bvar : T -> Ty -> Pat T 1
    | unit : Pat T 0 
    | variant : String -> Pat T 0 
    | record {n : Nat} : PatRec T n -> Pat T n 

  inductive PatRec : (T : Type) -> Nat -> Type where
    | single {n : Nat} : String -> Pat T n -> PatRec T n 
    | exten {n₁ n₂ : Nat} : String -> Pat T n₁ -> PatRec T n₂-> PatRec T (n₁ + n₂)
end

/-
t ::=                             term
  _                               hole 
  x                               variable
  ()                              unit
  #l t                            variant
  fs                              record
  cs                              function
  t.l                             projection
  t t                             application
  let x : τ = t in t              binding
  fix t                           recursion

cs ::=                            cases
  for p => t                      singleton 
  cs for p => t                   extension 

fs ::=                            fields 
  .l t                            singleton 
  fs .l t                         extension
-/

mutual
  inductive Tm (T : Type): Type
    | hole : Tm T 
    | bvar : T -> Tm T 
    | fvar : Nat -> Tm T 
    | unit : Tm T
    | variant : String -> Tm T -> Tm T
    | record : List (String × Tm T) -> Tm T
    | func : List (Σ n, Case T n) -> Tm T
    | proj : Tm T -> String -> Tm T
    | app : Tm T -> Tm T -> Tm T
    | letb : Tm T -> Ty -> (T -> Tm T) -> Tm T
    | fix : Tm T -> Tm T

  inductive Case (T : Type) : Nat -> Type
    | mk {n : Nat} : Pat T n -> Tm T -> Case T n

end


/-

m ::=                             substitution map
  ⬝                                empty
  α / τ :: m                      extension

Γ ::=                             typing environment 
  ⬝                                empty
  x : τ :: Γ                      extension

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

consistent constraint subtyping   
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


  {α ≤ τ} ⊆ Δ
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


  Δ ⊢ τ₁' ≤ τ₁ 
  Δ ⊢ τ₂' ≤ τ₂ 
---
Δ ⊢ τ₁ -> τ₂' ≤ τ₁' -> τ₂


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

constraint typing  
`Γ Δ C ⊢ t : τ`
```
TODO: fill in constraint typing rules
```

-/

-- static implementation 
/-


`merge Δ Δ = Δ`
```
merge op Δ₁ Δ₂ =
  fmap Δ₁ (α ≤ τ₁ =>
  fmap Δ₂ (β ≤ τ₂ =>
    {α ≤ τ₁ op (Δ₂ α), β ≤ (Δ₁ β) op τ₂}
  ))
```

`merge o[Δ] o[Δ] = o[Δ]`
```
merge _ none none = none 
merge _ none o = o 
merge _ o none = o 
merge op (some Δ₁) (some Δ₂) = some (merge op Δ₁ Δ₂)
```
-/


def lookup (key : Nat) : List (Nat × T) -> Option T
  | (k,v) :: bs => if key = k then some v else lookup key bs 
  | [] => none


#check List.bind
partial def merge (op : T -> T -> T) (df : T) (Δ₁ : List (Nat × T))  (Δ₂ : List (Nat × T)) : List (Nat × T) :=
  List.bind Δ₁ (fun (key₁, v₁) =>
  List.bind Δ₂ (fun (key₂, v₂) =>
    let uno := match lookup key₁ Δ₂ with
      | Option.some v₂ => [(key₁, op v₁ v₂)]
      | Option.none => [(key₁, op v₁ df)] 

    let dos := match lookup key₂ Δ₁ with
      | Option.some _ => [] 
      | Option.none => [(key₂, op v₂ df)]
    uno ++ dos
  ))


/-


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

`make_record_constraint Δ ⊢ τ * τ ≤ τ = o[C]`
```
make_record_constraint Δ ⊢ τ₀ * .l τ₁ & τ₂ ≤ μ α . τ =
  let β₁ = fresh in
  let C₁ = τ₁ ≤ ∀ {β₁ ≤ ?} ⟨(τ₀ & .l β₁ & τ₂) ≤ unroll (μ α . τ)⟩ . β₁ in
  C₁ ∧ make_record_constraint (Δ ⊢ τ₀ & .l τ₁ * τ₂ ≤ μ α . τ)

make_record_constraint Δ ⊢ τ₀ * .l τ₁ ≤ μ α . τ =
  let β₁ = fresh in
  let C₁ = τ₁ ≤ ∀ {β₁ ≤ ?} ⟨(τ₀ & .l β₁) ≤ unroll (μ α . τ)⟩ . β₁ in
  C₁

make_record_constraint _ ⊢ _ * _ ≤ _ = none
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
-/

/-

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
-/

-- occurs: check if free variable exists in type
mutual
  partial def Ty.occurs (key : Nat)  : Ty -> Bool 
    | [: ? :] => false 
    | .bvar id => false 
    | .fvar id => key = id 
    | .unit => false 
    | .variant l ty => (Ty.occurs key ty) 
    | .field l ty => (Ty.occurs key ty)
    | [: ⟨ty₁⟩ ∪ ⟨ty₂⟩ :] => (Ty.occurs key ty₁) ∨ (Ty.occurs key ty₂)
    -- | .union ty₁ ty₂ => (Ty.occurs key ty₁) ∨ (Ty.occurs key ty₂)
    | .inter ty₁ ty₂ => (Ty.occurs key ty₁) ∨ (Ty.occurs key ty₂)
    | .func ty₁ ty₂ => (Ty.occurs key ty₁) ∨ (Ty.occurs key ty₂)
    | .univ ctx c ty => (
      (List.any ctx (λ cty => Ty.occurs key cty)) ∨
      (Constr.occurs key c) ∨
      (Ty.occurs key ty)
    )
    | .induct ty => (Ty.occurs key ty)

  partial def Constr.occurs (key : Nat) : Constr -> Bool
    | Constr.tru => false 
    | Constr.subtype ty₁ ty₂ => (Ty.occurs key ty₁) ∨ (Ty.occurs key ty₂)
    | Constr.conj c₁ c₂ => (Constr.occurs key c₁) ∨ (Constr.occurs key c₂)
    | Constr.disj c₁ c₂ => (Constr.occurs key c₁) ∨ (Constr.occurs key c₂)
end

mutual
  partial def Ty.eq : Ty -> Ty -> Bool 
    | .unknown, .unknown => true 
    | .bvar id1, .bvar id2 => id1 = id2 
    | .fvar id1, .fvar id2 => id1 = id2 
    | .unit, .unit => true 
    | .variant l1 ty1, .variant l2 ty2 => 
      l1 = l2 ∧ (Ty.eq ty1 ty2) 
    | .field l1 ty1, .field l2 ty2 =>
      l1 = l2 ∧ (Ty.eq ty1 ty2) 
    | .union ty₁ ty₂, .union ty₃ ty₄ => 
      (Ty.eq ty₁ ty₃) ∧ (Ty.eq ty₂ ty₄)
    | .inter ty₁ ty₂, .inter ty₃ ty₄ => 
      (Ty.eq ty₁ ty₃) ∧ (Ty.eq ty₂ ty₄)
    | .func ty₁ ty₂, .func ty₃ ty₄  => 
      (Ty.eq ty₁ ty₃) ∧ (Ty.eq ty₂ ty₄)
    | .univ ctx₁ c₁ ty₁, .univ ctx₂ c₂ ty₂ =>
      (List.isEqv ctx₁ ctx₂ (fun cty₁ cty₂ => Ty.eq cty₁ cty₂)) ∧
      (Constr.eq c₁ c₂) ∧ (Ty.eq ty₁ ty₂)
    | .induct ty₁, .induct ty₂ => (Ty.eq ty₁ ty₂)
    | _, _ => false

  partial def Constr.eq : Constr -> Constr -> Bool
    | Constr.tru, Constr.tru => true 
    | Constr.subtype ty₁ ty₂, Constr.subtype ty₃ ty₄ => 
      (Ty.eq ty₁ ty₃) ∧ (Ty.eq ty₂ ty₄)
    | Constr.conj c₁ c₂, Constr.conj c₃ c₄ =>
      (Constr.eq c₁ c₃) ∧ (Constr.eq c₂ c₄)
    | Constr.disj c₁ c₂, Constr.disj c₃ c₄ =>
      (Constr.eq c₁ c₃) ∧ (Constr.eq c₂ c₄)
    | _, _ => false
end




mutual


  partial def Ty.free_subst (m : List (Nat × Ty)) : Ty -> Ty
    | .unknown => .unknown 
    | .bvar id => .bvar id 
    | .fvar id => (match lookup id m with
      | some ty => ty 
      | none => .fvar id
    )
    | .unit => .unit
    | .variant l ty => .variant l (Ty.free_subst m ty) 
    | .field l ty => .field l (Ty.free_subst m ty)
    | .union ty₁ ty₂ => .union (Ty.free_subst m ty₁) (Ty.free_subst m ty₂)
    | .inter ty₁ ty₂ => .inter (Ty.free_subst m ty₁) (Ty.free_subst m ty₂)
    | .func ty₁ ty₂ => .func (Ty.free_subst m ty₁) (Ty.free_subst m ty₂)
    | .univ ctx c ty => (.univ
      (List.map (λ cty => Ty.free_subst m cty) ctx) 
      (Constr.free_subst m c) 
      (Ty.free_subst m ty)
    )
    | .induct ty => .induct (Ty.free_subst m ty)

  partial def Constr.free_subst (m : List (Nat × Ty)) : Constr -> Constr
    | Constr.tru => Constr.tru
    | Constr.subtype ty₁ ty₂ => Constr.subtype (Ty.free_subst m ty₁) (Ty.free_subst m ty₂)
    | Constr.conj c₁ c₂ => Constr.conj (Constr.free_subst m c₁) (Constr.free_subst m c₂)
    | Constr.disj c₁ c₂ => Constr.disj (Constr.free_subst m c₁) (Constr.free_subst m c₂)
end


declare_syntax_cat sub
syntax slm "/" slm : sub 
syntax "[" sub,+ "]" : sub
syntax "[sub:" sub ":]" : term 

macro_rules
  | `([sub: $a:slm / $b:slm :]) => `(([: $a :], [: $b :])) 

macro_rules
  | `([sub: [$x:sub] :]) => `([ [sub: $x :] ])
  | `([sub: [$x,$xs:sub,*] :]) => `([sub: $x :] :: [sub: [$xs,*] :])


syntax slm "%" sub : slm 
macro_rules
  | `([: $a % $b:sub :]) => `(Ty.free_subst [sub: $b :] [: $a :])


-- #check [: (£1) % [1 / ?] :]
#check [: (£1) % [1/?] :]

#check Fin

mutual
  partial def Ty.raise_binding (start : Nat) (args : List Ty) : Ty -> Ty
    | .unknown => .unknown 
    | .bvar id => 
        if h : start ≤ id ∧ (id - start) < args.length then
          let i : Fin args.length := {
            val := (id - start),
            isLt := (match h with | And.intro _ h' => h') 
          } 
          args.get i 
        else
          .bvar id
    | .fvar id => .fvar id 
    | .unit => .unit
    | .variant l ty => .variant l (Ty.raise_binding start args ty) 
    | .field l ty => .field l (Ty.raise_binding start args ty)
    | .union ty₁ ty₂ => .union (Ty.raise_binding start args ty₁) (Ty.raise_binding start args ty₂)
    | .inter ty₁ ty₂ => .inter (Ty.raise_binding start args ty₁) (Ty.raise_binding start args ty₂)
    | .func ty₁ ty₂ => .func (Ty.raise_binding start args ty₁) (Ty.raise_binding start args ty₂)
    | .univ ctx c ty => (.univ
      (List.map (λ cty => Ty.raise_binding (start + ctx.length) args cty) ctx) 
      (Constr.raise_binding (start + ctx.length) args c) 
      (Ty.raise_binding (start + ctx.length) args ty)
    )
    | .induct ty => .induct (Ty.raise_binding (start + 1) args ty)

  partial def Constr.raise_binding (start : Nat) (args : List Ty) : Constr -> Constr
    | .tru => .tru 
    | .subtype ty₁ ty₂ => .subtype (Ty.raise_binding start args ty₁) (Ty.raise_binding start args ty₂)
    | .conj c₁ c₂ => .conj (Constr.raise_binding start args c₁) (Constr.raise_binding start args c₂)
    | .disj c₁ c₂ => .disj (Constr.raise_binding start args c₁) (Constr.raise_binding start args c₂)
end

syntax slm "↑" slm "/" slm : slm 

macro_rules
  | `([: $a ↑ $b / $c :]) => `(Ty.raise_binding [: $b :] [: $c :] [: $a :])


def τ := [: ? :]
#check [: ⟨τ⟩ ↑ 0 / [μ 0 . ⟨τ⟩]:]

-- termination_by 
--   Ty.subst _ ty => (some ty, none)
--   Constr.subst _ c => (none, some c)
-- decreasing_by sorry


/-
`unroll μ α . τ = τ`
```
unroll μ α . τ = subst {α ≤ μ α . τ} τ
```
-/
partial def unroll (τ : Ty) : Ty := 
  -- Ty.raise_binding 0 [Ty.induct τ] τ 
  [: ⟨τ⟩ ↑ 0 / [μ 0 . ⟨τ⟩]:]

/-

`rename m Δ`
```
rename m Δ = 
  map Δ (α / τ =>
    let β = m α in
    {β / subst m τ}
  )
```
-/


/-
`roll α τ`
```
roll α τ = 
  μ α . τ
  if occurs α τ else
  τ
```
-/

mutual
  partial def Ty.lower_binding (depth : Nat) : Ty -> Ty
    | .unknown => .unknown 
    | .bvar id => .bvar (id + depth)
    | .fvar id => .fvar id 
    | .unit => .unit
    | .variant l ty => .variant l (Ty.lower_binding depth ty) 
    | .field l ty => .field l (Ty.lower_binding depth ty)
    | .union ty₁ ty₂ => .union (Ty.lower_binding depth ty₁) (Ty.lower_binding depth ty₂)
    | .inter ty₁ ty₂ => .inter (Ty.lower_binding depth ty₁) (Ty.lower_binding depth ty₂)
    | .func ty₁ ty₂ => .func (Ty.lower_binding depth ty₁) (Ty.lower_binding depth ty₂)
    | .univ ctx c ty => (.univ
      (List.map (λ cty => Ty.lower_binding (depth + ctx.length) cty) ctx) 
      (Constr.lower_binding (depth + ctx.length) c) 
      (Ty.lower_binding (depth + ctx.length) ty)
    )
    | .induct ty => .induct (Ty.lower_binding (depth + 1) ty)

  partial def Constr.lower_binding (depth : Nat) : Constr -> Constr
    | Constr.tru => Constr.tru
    | Constr.subtype ty₁ ty₂ => Constr.subtype (Ty.lower_binding depth ty₁) (Ty.lower_binding depth ty₂)
    | Constr.conj c₁ c₂ => Constr.conj (Constr.lower_binding depth c₁) (Constr.lower_binding depth c₂)
    | Constr.disj c₁ c₂ => Constr.disj (Constr.lower_binding depth c₁) (Constr.lower_binding depth c₂)
end

syntax slm "↓" num : slm 

macro_rules
  | `([: $b:slm ↓ $a:num :]) => `(Ty.lower_binding $a [: $b :])


partial def roll (key : Nat) (τ : Ty) : Ty :=
  if Ty.occurs key τ then
    [: (μ 0 . ⟨τ⟩↓1) % [⟨key⟩ / £0] :]
  else
    τ



/-
`Δ α = τ` 
```
Δ α =  
  τ
  if {α → τ} ⊆ Δ else
  ?
```

-/


def liberate (i : Nat) : List Ty -> List (Nat × Ty) 
  | [] => []
  | cty :: ctx => (i, cty) :: (liberate (i + 1) ctx)

def refresh (i : Nat) (ctx : List Ty) : (Nat × List (Nat × Ty) × List Ty) := 
  let args := (List.range ctx.length).map (fun j => .fvar (i + j))
  let f : Ty -> Ty := Ty.raise_binding 0 args 
  let Δ' := liberate i (ctx.map f)
  let i' := i + ctx.length
  (i', Δ', args)


def make_record_constraint_sub (prev_ty : Ty) : Ty -> Ty -> Option Constr
  | (.field l ty'), mu_ty => 
      let ty := .univ [Ty.unknown] (Constr.subtype 
        (Ty.inter (Ty.lower_binding 1 prev_ty) (.field l (.bvar 0))) (Ty.lower_binding 1 (unroll mu_ty))
      ) (.bvar 0)
      some (Constr.subtype ty' ty)
  | .inter (.field l ty') rem_ty, mu_ty => 
      let ty := 
      [: ∀ [?] ((⟨prev_ty⟩↓1 ∩ (#⟨l⟩ £0) ∩ ⟨rem_ty⟩↓1) ≤ ⟨unroll mu_ty⟩↓1) . £0 :]

      Option.bind (
        make_record_constraint_sub (Ty.inter prev_ty (.field l ty')) rem_ty mu_ty
      ) (fun rem =>
        some (Constr.conj (Constr.subtype ty' ty) rem
      ))
  | .inter rem_ty (.field l ty'), mu_ty => 
      -- copy and paste above case (for terminateion proved by structure)
      let ty := .univ [Ty.unknown] (Constr.subtype 
        (Ty.inter (
          Ty.inter (Ty.lower_binding 1 prev_ty) (.field l (.bvar 0))) 
          (Ty.lower_binding 1 rem_ty)
        ) (Ty.lower_binding 1 (unroll mu_ty))
      ) (.bvar 0)

      Option.bind (
        make_record_constraint_sub (Ty.inter prev_ty (.field l ty')) rem_ty mu_ty
      ) (fun rem =>
        some (Constr.conj (Constr.subtype ty' ty) rem
      ))
  | _, _ =>  none

def make_record_constraint_super (prev : Ty) : Ty -> Ty -> Option Constr
  | mu_ty, (.field l ty') => 
      let ty := .univ [Ty.unknown] (Constr.subtype 
        (Ty.lower_binding 1 (unroll mu_ty))
        (Ty.inter (Ty.lower_binding 1 prev) (.field l (.bvar 0))) 
      ) (.bvar 0)
      some (Constr.subtype ty' ty)
  | mu_ty, .inter (.field l ty') rem_ty => 
      let ty := .univ [Ty.unknown] (Constr.subtype 
        (Ty.lower_binding 1 (unroll mu_ty))
        (Ty.inter (
          Ty.inter (Ty.lower_binding 1 prev) (.field l (.bvar 0))) 
          (Ty.lower_binding 1 rem_ty)
        ) 
      ) (.bvar 0)

      Option.bind (
        make_record_constraint_super (Ty.inter prev (.field l ty')) mu_ty rem_ty
      ) (fun rem =>
        some (Constr.conj (Constr.subtype ty' ty) rem
      ))
  | mu_ty, .inter rem_ty (.field l ty') => 
      -- copy and paste above case (for terminateion proved by structure)
      let ty := .univ [Ty.unknown] (Constr.subtype 
        (Ty.lower_binding 1 (unroll mu_ty))
        (Ty.inter (
          Ty.inter (Ty.lower_binding 1 prev) (.field l (.bvar 0))) 
          (Ty.lower_binding 1 rem_ty)
        ) 
      ) (.bvar 0)

      Option.bind (
        make_record_constraint_super (Ty.inter prev (.field l ty')) mu_ty rem_ty
      ) (fun rem =>
        some (Constr.conj (Constr.subtype ty' ty) rem
      ))
  | _, _ =>  none


mutual
  partial def Ty.unify (i : Nat) (Δ : List (Nat × Ty)) : Ty -> Ty -> Option (Nat × List (Nat × Ty))

    | .fvar id, τ₂  => match lookup id Δ with 
      | none => some (i + 2, [(i, .inter (roll id τ₂) (Ty.fvar (i + 1)))]) 
      | some Ty.unknown => some (i + 2, [(i, .inter (roll id τ₂) (Ty.fvar (i + 1)))]) 
      | some τ₁ => Ty.unify i Δ τ₁ τ₂ 

    | τ₁, .fvar id  => match lookup id Δ with 
      | none => some (i + 2, [(i, .union (roll id τ₁) (Ty.fvar (i + 1)))]) 
      | some Ty.unknown => some (i + 2, [(i, .union (roll id τ₁) (Ty.fvar (i + 1)))]) 
      | some τ₂ => Ty.unify i Δ τ₁ τ₂ 

    | .induct τ', .induct τ =>
      Ty.unify i Δ τ' τ 

    | .variant l' τ', .induct τ =>
      Ty.unify i Δ (.variant l' τ') (unroll τ)

    | .induct τ', (.variant l τ) =>
      Ty.unify i Δ (unroll τ') (.variant l τ) 

    | τ', .induct τ =>
      Option.bind (make_record_constraint_sub Ty.unknown τ' τ) (fun c =>
        Constr.solve i Δ c
      )

    | .induct τ', τ =>
      Option.bind (make_record_constraint_super Ty.unknown τ' τ) (fun c =>
        Constr.solve i Δ c
      )

    | .union τ₁ τ₂, τ => 
      Constr.solve i Δ (Constr.conj 
        (Constr.subtype τ₁ τ)
        (Constr.subtype τ₂ τ)
      )

    | τ, .union τ₁ τ₂ => 
      Constr.solve i Δ (Constr.disj 
        (Constr.subtype τ τ₁)
        (Constr.subtype τ τ₂)
      )

    | τ, .inter τ₁ τ₂ => 
      Constr.solve i Δ (Constr.conj
        (Constr.subtype τ τ₁)
        (Constr.subtype τ τ₂)
      )

    | .inter τ₁ τ₂, τ => 
      Constr.solve i Δ (Constr.disj
        (Constr.subtype τ₁ τ)
        (Constr.subtype τ₂ τ)
      )

    | .func τ₁ τ₂', .func τ₁' τ₂ =>
      Constr.solve i Δ (Constr.conj
        (Constr.subtype τ₁' τ₁)
        (Constr.subtype τ₂' τ₂)
      )

    | .variant l' τ', .variant l τ =>
      if l' = l then
        Ty.unify i Δ τ' τ
      else
        none

    | .field l' τ', .field l τ =>
      if l' = l then
        Ty.unify i Δ τ' τ
      else
        none

    | ty, .univ ctx c τ =>
      let (i, Δ, args) := refresh i ctx
      let c := Constr.raise_binding 0 args c
      let τ := Ty.raise_binding 0 args τ
      Constr.solve i Δ (Constr.conj c (Constr.subtype ty τ))

    | .univ ctx c τ, ty =>
      let (i, Δ, args) := refresh i ctx
      let c := Constr.raise_binding 0 args c
      let τ := Ty.raise_binding 0 args τ
      Constr.solve i Δ (Constr.conj c (Constr.subtype τ ty))

    | .bvar id₁, .bvar id₂  =>
      if id₁ = id₂ then 
        some (i, [])
      else
        none

    | .unit, .unit => some (i, []) 
    | .unknown, _ => some (i, []) 
    | _, .unknown => some (i, []) 
    | _, _ => none

  partial def Constr.solve (i : Nat) (Δ : List (Nat × Ty)) : Constr -> Option (Nat × List (Nat × Ty))
    | Constr.tru => some (i, []) 
    | Constr.subtype ty₁ ty₂ => Ty.unify i Δ ty₁ ty₂
    | Constr.conj c₁ c₂ => 
        Option.bind (Constr.solve i Δ c₁) (fun (i, Δ₁) => 
        Option.bind (Constr.solve i Δ c₂) (fun (i, Δ₂) =>
          some (i, merge Ty.inter Ty.unknown Δ₁ Δ₂)
        ))
    | Constr.disj c₁ c₂ =>
        Option.bind (Constr.solve i Δ c₁) (fun (i, Δ₁) => 
        Option.bind (Constr.solve i Δ c₂) (fun (i, Δ₂) =>
          some (i, merge Ty.union Ty.unknown Δ₁ Δ₂)
        ))
end

/-

`solve Δ ⊢ C = o[Δ]`
```
solve Δ ⊢ C₁ ∧ C₂ =  
  merge & (solve Δ ⊢ C₁) (solve Δ ⊢ C₂)

solve Δ ⊢ C₁ ∨ C₂ = 
  merge | (solve Δ ⊢ C₁) (solve Δ ⊢ C₂)

solve Δ ⊢ α ≤ τ =
  let τ' = Δ α in (
    let β = fresh in some {α ≤ ((roll α τ) & β), β ≤ ?}
    if τ' = ? else
    solve Δ ⊢ τ' ≤ τ
  )

solve Δ ⊢ τ' ≤ α =
  let τ = Δ α in (
    let β = fresh in some {α ≤ ((roll α τ') | β), β ≤ ?}  
    if τ = ? else
    (solve Δ ⊢ τ' ≤ τ)
  )

solve Δ ⊢ (∀ Δ' ⟨C⟩ . τ') ≤ τ =
...

solve Δ ⊢ τ' ≤ (∀ Δ' ⟨C⟩ . τ) =
...

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


solve Δ ⊢ *l τ' ≤ μ α . τ =  
  solve Δ ⊢ *l τ' ≤ unroll (μ α . τ)  

solve Δ ⊢ μ α . τ' ≤ *l τ  =  
  solve Δ ⊢ unroll (μ α . τ') ≤ *l τ

solve Δ ⊢ .l τ' ≤ μ α . τ =  
  solve Δ ⊢ .l τ' ≤ unroll (μ α . τ)  

solve Δ ⊢ μ α . τ' ≤ .l τ  =  
  solve Δ ⊢ unroll (μ α . τ') ≤ .l τ


solve Δ ⊢ τ' ≤ μ α . τ =
  map (linearze_record τ') (τ' =>
  map (make_record_constraint Δ ⊢ . * τ' ≤ μ α . τ) (C =>
    solve Δ ⊢ C 
  ))

solve Δ ⊢ μ α . τ' ≤ τ  =  
  map (linearze_record τ') (τ' =>
  map (make_record_constraint Δ ⊢ . * μ α . τ' ≤ τ) (C =>
    solve Δ ⊢ C 
  ))

solve Δ ⊢ *l' τ' ≤ *l τ =
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
    some (Γ₁ ++ Γ₂)
  ))
...
```


`infer Γ Δ ⊢ t : τ = o[Δ;τ]`
```
TODO:
- raise type binding at application in "infer/generation of constrations"

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
  map (infer Γ (Δ ++ Δ') ⊢ t₁ : α) (Δ₁,τ₁ => 
    some (Δ' ++ Δ₁ , #l τ₁)
  ))

infer Γ Δ ⊢ (for t₁ : τ₁ => t₂) : τ =
  let Δ₁, τ₁ = τ₁[?/fresh] in
  let Γ₁ = patvars t₁ τ₁ in
  let β = fresh in
  map (solve Δ ⊢ (∀ Δ₁ ++ {β} . τ₁ -> β) ≤ τ) (Δ' => 
  map (infer (Γ ++ Γ₁) (Δ ++ Δ') ⊢ t₂ : β) (Δ₂', τ₂' =>
    -- patvars (Γ₁) are NOT generalized in τ₂'
    some (Δ' ++ Δ₂' , τ₁ -> τ₂')
  ))


infer Γ Δ ⊢ (for t₁ : τ₁ => t₂) cs : τ =
  map (infer Γ Δ ⊢ (for t₁ : τ₁ => t₂) : τ) (Δ', τ' =>
  map (infer Γ Δ ++ Δ' ⊢ cs : τ₂) (Δ'', τ'' => 
    some (Δ' ++ Δ'' , τ' & τ'')
  ))

infer Γ Δ ⊢ t t₁ : τ₂ =
  map (infer Γ Δ ⊢ t : ? -> τ₂ in) (Δ',τ' => 
  map (functify τ') (τ₁,τ₂' => 
  -- break type (possibly intersection) into premise and conclusion 
  map (infer Γ (Δ ++ Δ') ⊢ t₁ : τ₁) (Δ₁',τ₁' =>
  map (solve Δ ++ Δ' ++ Δ₁' ⊢ τ' ≤ (τ₁' -> τ₂)) (Δ' =>
    some(Δ' , τ₂' & τ₂)
  ))))

infer Γ Δ ⊢ (.l t₁) : τ =
  let α = fresh in
  map (solve Δ ⊢ (∀ {α} . (.l α)) ≤ τ) (Δ' =>
  map (infer Γ (Δ ++ Δ') ⊢ t₁ : α) (Δ₁ , τ₁ =>  
    some(Δ' ++ Δ₁ , .l τ₁)
  ))

infer Γ Δ ⊢ (.l t₁) fs : τ =
  map (infer Γ Δ ⊢ (.l t₁) : τ) (Δ' , τ' =>
  map (infer Γ (Δ ++ Δ') ⊢ fs : τ) (Δ'' , τ'' =>
    some(Δ' ++ Δ'' , τ' & τ'')
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
  map (infer (Γ ++ {x : (∀ Δ₁' . τ₁')}) Δ ⊢ t₂ : τ₂) (Δ₂' , τ₂' =>
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
