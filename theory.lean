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
  | univ : Nat -> Ty × Ty -> Ty -> Ty
  | exis : Nat -> Ty × Ty -> Ty -> Ty
  | recur : Ty -> Ty


declare_syntax_cat slm
syntax num : slm 
syntax ident : slm
syntax "[" slm,+ "]" : slm 
syntax "£"slm:90 : slm
syntax "@"slm:90 : slm
syntax "♢" : slm
syntax "#"slm:90 slm : slm
syntax "."slm:90 slm : slm
syntax "?" : slm
syntax:50 slm:50 "->" slm:51 : slm
syntax:60 slm:60 "∪" slm:61 : slm
syntax:60 slm:60 "+" slm:61 : slm
syntax:70 slm:70 "∩" slm:71 : slm
syntax:70 slm:70 "×" slm:71 : slm
syntax "∀" slm "|" slm "<:" slm "." slm : slm 
syntax "∀" slm "." slm : slm 
syntax "∃" slm "|" slm "<:" slm  "." slm : slm 
syntax "∃" slm "." slm : slm 
syntax "μ 0 ." slm : slm 

syntax:50 slm:50 "⊆" slm:51 : slm

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
  | `([: ♢ :]) => `(Ty.unit)
  | `([: #$a $b:slm :]) => `(Ty.variant [: $a :] [: $b :])
  | `([: .$a $b:slm :]) => `(Ty.field [: $a :] [: $b :])
  | `([: ? :]) => `(Ty.unknown)
  | `([: $a -> $b :]) => `(Ty.func [: $a :] [: $b :])
  | `([: $a ∪ $b :]) => `(Ty.union [: $a :] [: $b :])
  | `([: $a + $b :]) => `(Ty.union [: #inl $a :] [: #inr $b :])
  | `([: $a ∩ $b :]) => `(Ty.inter [: $a :] [: $b :])
  | `([: $a × $b :]) => `(Ty.inter [: .left $a :] [: .right $b :])
  | `([: ∀ $a | $b <: $c . $d :]) => `(Ty.univ [: $a :] ([: $b :], [: $c :]) [: $d :])
  | `([: ∀ $a:slm . $b:slm :]) => `(Ty.univ [: $a :] ([: £$a :], [: ? :]) [: $b :] )
  | `([: ∃ $a | $b <: $c . $d  :]) => `(Ty.exis [: $a :] ([: $b :], [: $c :]) [: $d :])
  | `([: ∃ $a:slm . $b:slm :]) => `(Ty.exis [: $a :] ([: £$a :], [: ? :]) [: $b :] )
  | `([: μ 0 . $a :]) => `(Ty.recur [: $a :])

-- generic
  | `([: ($a) :]) => `([: $a :])

--escape 
  | `([: ⟨ $e ⟩ :]) => pure e

#check [: £0 ∪ ? :]
#check [: £0 ∩ ? :]
#check [: £0 × ? :]
#check [: £0 + ? :]
def x := 0
#check [: ∀ 1 | £0 <: ? . £⟨x⟩ :]
#check [: ∀ 1 | £0 <: ? . £0 :]
#check [: ∀ 2 | ? <: ? . £0 :]
#check [: ∀ 2 . £0 :]
#check [: ♢ :]
#check [: @24 :]
#check [: #foo ♢ ∪ #boo ♢ :]
#check [: μ 0 . #foo £0 :]
#check [: μ 0 . #foo £0  ∩ ? ∪ @2 ∩ ?:]
#check [: £3 ∩ ? -> @1 ∪ @2 :]
#check [: μ 0 . #foo £0  ∩ ? ∪ @2 ∩ ? -> @1 ∪ @2 :]
#check [: μ 0 . #foo £0  ∩ ? ∪ @2 ∩ ? :]
#check [: ? :]

def lookup (key : Nat) : List (Nat × T) -> Option T
  | (k,v) :: bs => if key = k then some v else lookup key bs 
  | [] => none


partial def merge (op : T -> T -> T) (df : T) (Δ₁ : List (Nat × T))  (Δ₂ : List (Nat × T)) : List (Nat × T) :=
  List.bind Δ₁ (fun (key₁, v₁) =>
  List.bind Δ₂ (fun (key₂, v₂) =>
    let uno := match lookup key₁ Δ₂ with
      | some v₂ => [(key₁, op v₁ v₂)]
      | none => [(key₁, op v₁ df)] 

    let dos := match lookup key₂ Δ₁ with
      | some _ => [] 
      | none => [(key₂, op v₂ df)]
    uno ++ dos
  ))

/-
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

well_founded α ∀ Δ ⟨τ' ⊆ α⟩ . τ = 
  α ∈ Δ orelse
  decreasing τ τ' 
```
-/

def Ty.occurs (key : Nat)  : Ty -> Bool 
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
  | .univ n (cty1, cty2) ty => (Ty.occurs key cty1) ∨ (Ty.occurs key cty2) ∨ (Ty.occurs key ty)
  | .exis n (cty1, cty2) ty => (Ty.occurs key cty1) ∨ (Ty.occurs key cty2) ∨ (Ty.occurs key ty)
  | .recur ty => (Ty.occurs key ty)

def Ty.free_subst (m : List (Nat × Ty)) : Ty -> Ty
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
  | .univ n (ct1, ct2) ty => (.univ
    n
    (Ty.free_subst m ct1, Ty.free_subst m ct2) 
    (Ty.free_subst m ty)
  )
  | .exis n (ct1, ct2) ty => (.exis
    n
    (Ty.free_subst m ct1, Ty.free_subst m ct2) 
    (Ty.free_subst m ty)
  )
  | .recur ty => .recur (Ty.free_subst m ty)


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

def Ty.raise_binding (start : Nat) (args : List Ty) : Ty -> Ty
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
  | .univ n (ct1, ct2) ty => (.univ
    n
    (Ty.raise_binding (start + n) args ct1, Ty.raise_binding (start + n) args ct2)
    (Ty.raise_binding (start + n) args ty)
  )
  | .exis n (ct1, ct2) ty => (.exis
    n
    (Ty.raise_binding (start + n) args ct1, Ty.raise_binding (start + n) args ct2)
    (Ty.raise_binding (start + n) args ty)
  )
  | .recur ty => .recur (Ty.raise_binding (start + 1) args ty)

syntax slm "↑" slm "/" slm : slm 

macro_rules
  | `([: $a ↑ $b / $c :]) => `(Ty.raise_binding [: $b :] [: $c :] [: $a :])


def τ := [: ? :]
#check [: ⟨τ⟩ ↑ 0 / [μ 0 . ⟨τ⟩]:]


partial def unroll (τ : Ty) : Ty := 
  -- Ty.raise_binding 0 [Ty.recur τ] τ 
  [: ⟨τ⟩ ↑ 0 / [μ 0 . ⟨τ⟩]:]

def Ty.lower_binding (depth : Nat) : Ty -> Ty
  | .unknown => .unknown 
  | .bvar id => .bvar (id + depth)
  | .fvar id => .fvar id 
  | .unit => .unit
  | .variant l ty => .variant l (Ty.lower_binding depth ty) 
  | .field l ty => .field l (Ty.lower_binding depth ty)
  | .union ty₁ ty₂ => .union (Ty.lower_binding depth ty₁) (Ty.lower_binding depth ty₂)
  | .inter ty₁ ty₂ => .inter (Ty.lower_binding depth ty₁) (Ty.lower_binding depth ty₂)
  | .func ty₁ ty₂ => .func (Ty.lower_binding depth ty₁) (Ty.lower_binding depth ty₂)
  | .univ n (ct1, ct2) ty => (.univ
    n
    (Ty.lower_binding (depth + n) ct1, Ty.lower_binding (depth + n) ct2)
    (Ty.lower_binding (depth + n) ty)
  )
  | .exis n (ct1, ct2) ty => (.exis
    n
    (Ty.lower_binding (depth + n) ct1, Ty.lower_binding (depth + n) ct2)
    (Ty.lower_binding (depth + n) ty)
  )
  | .recur ty => .recur (Ty.lower_binding (depth + 1) ty)

syntax slm "↓" num : slm 

macro_rules
  | `([: $b:slm ↓ $a:num :]) => `(Ty.lower_binding $a [: $b :])


partial def roll (key : Nat) (τ : Ty) : Ty :=
  if Ty.occurs key τ then
    [: (μ 0 . ⟨τ⟩↓1) % [⟨key⟩ / £0] :]
  else
    τ


def liberate (i : Nat) : Nat -> List (Nat × Ty) 
  | 0 => []
  | n + 1 => (i, [: ? :]) :: (liberate (i + 1) n)

def refresh (i : Nat) (n : Nat) : (Nat × List (Nat × Ty) × List Ty) := 
  let args := (List.range n).map (fun j => .fvar (i + j))
  let Δ' :=  liberate i n 
  let i' := i + n 
  (i', Δ', args)


def make_record_constraint_sub (prev_ty : Ty) : Ty -> Ty -> List (Ty × Ty) 
  | (.field l ty'), mu_ty => 
      let ty := .exis 1 ( 
        (Ty.inter (Ty.lower_binding 1 prev_ty) (.field l (.bvar 0))),
        (Ty.lower_binding 1 (unroll mu_ty))
      ) (.bvar 0)
      [(ty', ty)]
  | .inter (.field l ty') rem_ty, mu_ty => 
      let ty := 
      [: ∃ 1 | (⟨prev_ty⟩↓1 ∩ (#⟨l⟩ £0) ∩ ⟨rem_ty⟩↓1) <: ⟨unroll mu_ty⟩↓1 . £0 :]

      let rem := make_record_constraint_sub (Ty.inter prev_ty (.field l ty')) rem_ty mu_ty
      if rem.length = 0 then
        []
      else 
        (ty', ty) :: rem
  | .inter rem_ty (.field l ty'), mu_ty => 
      -- copy and paste above case (for terminateion proved by structure)
      let ty := .exis 1 ( 
        (Ty.inter (
          Ty.inter (Ty.lower_binding 1 prev_ty) (.field l (.bvar 0))) 
          (Ty.lower_binding 1 rem_ty)
        ),
         (Ty.lower_binding 1 (unroll mu_ty))
      ) (.bvar 0)

      let rem := make_record_constraint_sub (Ty.inter prev_ty (.field l ty')) rem_ty mu_ty
      if rem.length = 0 then
        []
      else 
        (ty', ty) :: rem
  | _, _ => [] 

def make_record_constraint_super (prev : Ty) : Ty -> Ty -> List (Ty × Ty) 
  | mu_ty, (.field l ty') => 
      let ty := .exis 1 ( 
        (Ty.lower_binding 1 (unroll mu_ty)),
        (Ty.inter (Ty.lower_binding 1 prev) (.field l (.bvar 0))) 
      ) (.bvar 0)
      [(ty', ty)]
  | mu_ty, .inter (.field l ty') rem_ty => 
      let ty := .exis 1 (
        (Ty.lower_binding 1 (unroll mu_ty)),
        (Ty.inter (
          Ty.inter (Ty.lower_binding 1 prev) (.field l (.bvar 0))) 
          (Ty.lower_binding 1 rem_ty)
        ) 
      ) (.bvar 0)

      let rem := make_record_constraint_super (Ty.inter prev (.field l ty')) mu_ty rem_ty
      if rem.length = 0 then
        []
      else
        (ty', ty) :: rem
  | mu_ty, .inter rem_ty (.field l ty') => 
      -- copy and paste above case (for terminateion proved by structure)
      let ty := .exis 1 ( 
        (Ty.lower_binding 1 (unroll mu_ty)),
        (Ty.inter (
          Ty.inter (Ty.lower_binding 1 prev) (.field l (.bvar 0))) 
          (Ty.lower_binding 1 rem_ty)
        ) 
      ) (.bvar 0)

      let rem := make_record_constraint_super (Ty.inter prev (.field l ty')) mu_ty rem_ty
      if rem.length = 0 then
        []
      else
        (ty', ty) :: rem
  | _, _ => [] 


partial def Ty.unify (i : Nat) (Δ : List (Nat × Ty)) : Ty -> Ty -> Option (Nat × List (Nat × Ty))

  | .fvar id, τ₂  => match lookup id Δ with 
    | none => some (i + 2, [(i, .inter (roll id τ₂) (Ty.fvar (i + 1)))]) 
    | some Ty.unknown => some (i + 2, [(i, .inter (roll id τ₂) (Ty.fvar (i + 1)))]) 
    | some τ₁ => Ty.unify i Δ τ₁ τ₂ 

  | τ₁, .fvar id  => match lookup id Δ with 
    | none => some (i + 2, [(i, .union (roll id τ₁) (Ty.fvar (i + 1)))]) 
    | some Ty.unknown => some (i + 2, [(i, .union (roll id τ₁) (Ty.fvar (i + 1)))]) 
    | some τ₂ => Ty.unify i Δ τ₁ τ₂ 

  | .recur τ', .recur τ =>
    Ty.unify i Δ τ' τ 

  | .variant l' τ', .recur τ =>
    Ty.unify i Δ (.variant l' τ') (unroll τ)

  | .recur τ', (.variant l τ) =>
    Ty.unify i Δ (unroll τ') (.variant l τ) 


  -- TODO: check function against induction type 

  | τ', .recur τ =>
    let cs := (make_record_constraint_sub Ty.unknown τ' τ)
    if cs.length = 0 then
      none
    else
      List.foldl (fun 
        | some (i, Δ), (ct1, ct2) => Ty.unify i Δ ct1 ct2
        | none, _ => none
      ) (some (i, Δ)) cs

  | .recur τ', τ =>
    let cs := (make_record_constraint_super Ty.unknown τ' τ) 
    if cs.length = 0 then
      none
    else
      List.foldl (fun 
        | some (i, Δ), (ct1, ct2) => Ty.unify i Δ ct1 ct2
        | none, _ => none
      ) (some (i, Δ)) cs

  | .union τ₁ τ₂, τ => 
    bind (Ty.unify i Δ τ₁ τ) (fun (i, Δ') => 
    bind (Ty.unify i Δ' τ₂ τ) (fun (i, Δ'') =>
      some (i, merge Ty.inter Ty.unknown Δ' Δ'')
    ))

  | τ, .union τ₁ τ₂ => 
    bind (Ty.unify i Δ τ τ₁) (fun (i, Δ₁) => 
    bind (Ty.unify i Δ τ τ₂) (fun (i, Δ₂) =>
      some (i, merge Ty.union Ty.unknown Δ₁ Δ₂)
    ))

  | τ, .inter τ₁ τ₂ => 
    bind (Ty.unify i Δ τ τ₁) (fun (i, Δ') => 
    bind (Ty.unify i Δ' τ τ₂) (fun (i, Δ'') =>
      some (i, merge Ty.inter Ty.unknown Δ' Δ'')
    ))

  | .inter τ₁ τ₂, τ => 
    bind (Ty.unify i Δ τ₁ τ) (fun (i, Δ₁) => 
    bind (Ty.unify i Δ τ₂ τ) (fun (i, Δ₂) =>
      some (i, merge Ty.union Ty.unknown Δ₁ Δ₂)
    ))

  | .func τ₁ τ₂', .func τ₁' τ₂ =>
    bind (Ty.unify i Δ τ₁' τ₁) (fun (i, Δ') => 
    bind (Ty.unify i Δ' τ₂' τ₂) (fun (i, Δ'') =>
      some (i, merge Ty.inter Ty.unknown Δ' Δ'')
    ))

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

  -- TODO: check subtyping for universals without unification 

  | ty, .exis n (ct1, ct2) τ =>
    let (i, Δ, args) := refresh i n 
    let ct1 := Ty.raise_binding 0 args ct1
    let ct2 := Ty.raise_binding 0 args ct2
    let τ := Ty.raise_binding 0 args τ
    bind (Ty.unify i Δ ct1 ct2) (fun (i, Δ') => 
    bind (Ty.unify i Δ' ty τ) (fun (i, Δ'') =>
      some (i, merge Ty.inter Ty.unknown Δ' Δ'')
    ))

  | .exis n (ct1, ct2) τ, ty =>
    let (i, Δ, args) := refresh i n 
    let ct1 := Ty.raise_binding 0 args ct1
    let ct2 := Ty.raise_binding 0 args ct2
    let τ := Ty.raise_binding 0 args τ
    bind (Ty.unify i Δ ct1 ct2) (fun (i, Δ') => 
    bind (Ty.unify i Δ' ty τ) (fun (i, Δ'') =>
      some (i, merge Ty.inter Ty.unknown Δ' Δ'')
    ))

  | .bvar id₁, .bvar id₂  =>
    if id₁ = id₂ then 
      some (i, [])
    else
      none

  | .unit, .unit => some (i, []) 
  | .unknown, _ => some (i, []) 
  | _, .unknown => some (i, []) 
  | _, _ => none


-- inductive PatRec : (T : Type) -> Nat -> Type where
--   | single {n : Nat} : String -> Pat T n -> PatRec T n 
--   | exten {n₁ n₂ : Nat} : String -> Pat T n₁ -> PatRec T n₂-> PatRec T (n₁ + n₂)

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
  cs ; for p => t                 extension 

fs ::=                            fields 
  .l t                            singleton 
  fs ; .l t                       extension
-/


/-

m ::=                             substitution map
  ⬝                                empty
  α / τ :: m                      extension

Γ ::=                             typing environment 
  ⬝                                empty
  x : τ :: Γ                      extension

-/

inductive Tm : Type
  | hole : Tm 
  | bvar : Nat -> Tm 
  | fvar : Nat -> Tm 
  | unit : Tm
  | variant : String -> Tm -> Tm
  | record : List (String × Tm) -> Tm
  | func : List (Tm × Tm) -> Tm
  | proj : Tm -> String -> Tm
  | app : Tm -> Tm -> Tm
  | letb : Tm -> Ty -> Tm -> Tm
  | fix : Tm -> Tm

/-

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
-/

/-

`infer Γ Δ ⊢ t : τ = o[Δ;τ]`
```

infer Γ Δ ⊢ () : τ =
  map (solve Δ ⊢ C ∧ [] ⊆ τ in) (Δ' =>
    some (Δ' , [])
  )
```
-/

def infer 
  (i : Nat)
  (Δ : List (Nat × Ty)) (Γ : List (Nat × Ty)) (t : Tm) (ty : Ty) : 
  Option (Nat × List (Nat × Ty) × Ty) := match t with
  | .unit => bind (Ty.unify i Δ Ty.unit ty) (fun (i, Δ) =>
      (i, Δ, Ty.unit)
    )
  | .bvar _ => none
  | .fvar x =>
    bind (lookup x Γ) (fun ty' =>
      -- TODO: instantiate/raise universal with free var
    )  
  | _ => none

/-
```

infer Γ Δ ⊢ x : τ = 
  let τ' = Γ x in
  let Δ', C, τ' = refresh τ' in
  map (solve Δ, Δ' ⊢ C ∧ τ' ⊆ τ) (Δ' =>
    some (Δ' , τ')
  )

infer Γ Δ ⊢ (#l t₁) : τ =
  let α = fresh in
  map (solve Δ ⊢ (∀ {α} . (#l α)) ⊆ τ) (Δ' => 
  map (infer Γ (Δ ++ Δ') ⊢ t₁ : α) (Δ₁,τ₁ => 
    some (Δ' ++ Δ₁ , #l τ₁)
  ))

infer Γ Δ ⊢ (for t₁ : τ₁ => t₂) : τ =
  let Δ₁, τ₁ = τ₁[?/fresh] in
  let Γ₁ = patvars t₁ τ₁ in
  let β = fresh in
  map (solve Δ ⊢ (∀ Δ₁ ++ {β} . τ₁ -> β) ⊆ τ) (Δ' => 
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
  map (solve Δ ++ Δ' ++ Δ₁' ⊢ τ' ⊆ (τ₁' -> τ₂)) (Δ' =>
    some(Δ' , τ₂' & τ₂)
  ))))

infer Γ Δ ⊢ (.l t₁) : τ =
  let α = fresh in
  map (solve Δ ⊢ (∀ {α} . (.l α)) ⊆ τ) (Δ' =>
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
      -- solve _ ⊢ nat ⊆ str = none
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
    -- infer {x : α} {α ⊆ ?} ⊢ (i2n x, s2n x) : _ = some _ , nat;nat
    -- solve {α ⊆ ?} ⊢ α ⊆ int = some {α ⊆ int & ?}  
    -- solve {α ⊆ int & ?} ⊢ α ⊆ str = some {α ⊆ int & str & ?}  
      -- solve {α ⊆ int & β, β ⊆ ?} ⊢ int & β ⊆ str = some {β ⊆ str & ?}  
        -- solve {...} ⊢ int ⊆ str ∨ β ⊆ str = some {β ⊆ str & ?}  
          -- solve {...} ⊢ β ⊆ str = some {β ⊆ str & ?}  

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
    -- solve {α ⊆ ?} ⊢ int ⊆ α = some {α ⊆ int | ?} 
    -- solve {α ⊆ int | ?} ⊢ str ⊆ α = some {α ⊆ int | str | ?} 
      -- solve {α ⊆ int | β, β ⊆ ?} ⊢ str ⊆ int | β  = some {β ⊆ str | ?} 
        -- solve {...} ⊢ str ⊆ int ∨ str ⊆ β = some {β ⊆ str | ?}
          -- solve {...} ⊢ str ⊆ β = some {β ⊆ str | ?}
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
  ∃ {list,nat} [list;nat] ⊆ list_len
    [#cons[α;list] ; #succ[nat]]
```


```
μ nat_list .
  [#zero[] ; #nil[]] |
  ∃ {nat,list} [nat;list] ⊆ nat_list .
    [#succ[nat] ; #cons[α;list]]
```

-- equivalent to the notion
```
  [#nil[] ; #zero[]] ⊆ list_len ∧

  ∀ list;nat ,
    ([list;nat] ⊆ list_len --> [#cons[α;list] ; #succ[nat]] ⊆ list_len)
```

-- related to the sigma type from dependent type theory
```
type dlist (n ⊆ nat) := list for n;list ⊆ nat_list 

(Σ n ⊆ nat . dlist n) ≡ nat_list 

(Σ n ⊆ nat . list for n;list ⊆ nat_list . list) ≡ nat_list 
```


### function induction type 

```
μ list_to_len .
  [#nil[] -> #zero[]] & 
  ∀ {list,nat} [list -> nat] ⊆ list_to_len .  
    [#cons[α;list] -> #succ[nat]]
```

```
μ nat_to_list .
  [#nil[] -> #zero[]] & 
  ∀ {nat,list} [nat -> list] ⊆ nat_to_list .  
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

  -- infer {f : α} _ ⊢ (f one) = some {α ⊆ nat -> ?} , _

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

/-
- consider adding relative complement type 
  - i.e. binary negation type operator
  - i.e. (τ₁ \ τ₂) ⊆ (τ₁ & ¬ τ₂), where ⊤ / τ₂ = ¬ τ₂)
-/
