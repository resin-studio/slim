inductive Ty : Type
  | dynamic : Ty
  | bvar : Nat -> Ty  
  | fvar : Nat -> Ty
  | unit : Ty
  | tag : String -> Ty -> Ty
  | field : String -> Ty -> Ty
  | union : Ty -> Ty -> Ty
  | inter : Ty -> Ty -> Ty
  | case : Ty -> Ty -> Ty
  | univ : Nat -> Ty × Ty -> Ty -> Ty
  | exis : Nat -> Ty × Ty -> Ty -> Ty
  | recur : Ty -> Ty
  | corec : Ty -> Ty
  deriving Repr

open Std

def Ty.repr [Repr α] (ty : Ty) (n : Nat) : Format :=
  -- let _ : ToFormat α := ⟨repr⟩
  match ty, n with
    | _ , _ => ""
    -- | .dynamic, _ => Format.text "?" 
    -- | .bvar : Nat -> Ty  
    -- | .fvar : Nat -> Ty
    -- | .unit : Ty
    -- | .tag : String -> Ty -> Ty
    -- | .field : String -> Ty -> Ty
    -- | .union : Ty -> Ty -> Ty
    -- | .inter : Ty -> Ty -> Ty
    -- | .case : Ty -> Ty -> Ty
    -- | .univ : Nat -> Ty × Ty -> Ty -> Ty
    -- | .exis : Nat -> Ty × Ty -> Ty -> Ty
    -- | .recur : Ty -> Ty
    -- | .corec : Ty -> Ty

-- instance : Repr Ty where 
--   def reprPrec ty n := Ty.to_string ty n


declare_syntax_cat slm
syntax num : slm 
syntax ident : slm
syntax "[" slm,+ "]" : slm 
syntax "£"slm:90 : slm
syntax "@"slm:90 : slm
syntax "♢" : slm
syntax "#"slm:90 slm:90 : slm
syntax "."slm:90 slm:90 : slm
syntax "?" : slm
syntax:50 slm:50 "->" slm:51 : slm
syntax:60 slm:60 "|" slm:61 : slm
syntax:60 slm:60 "+" slm:61 : slm
syntax:64 "∃" slm "::" slm "≤" slm  "." slm:65 : slm 
syntax:64 "∃" slm "." slm:65 : slm 
syntax:70 slm:70 "&" slm:71 : slm
syntax:70 slm:70 "×" slm:71 : slm
syntax:74 "∀" slm "::" slm "≤" slm "." slm:75 : slm 
syntax:74 "∀" slm "." slm:75 : slm 
syntax "μ 1 ." slm : slm 
syntax "ν 1 ." slm : slm 

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
  | `([: #$a $b:slm :]) => `(Ty.tag [: $a :] [: $b :])
  | `([: .$a $b:slm :]) => `(Ty.field [: $a :] [: $b :])
  | `([: ? :]) => `(Ty.dynamic)
  | `([: $a -> $b :]) => `(Ty.case [: $a :] [: $b :])
  | `([: $a | $b :]) => `(Ty.union [: $a :] [: $b :])
  | `([: $a + $b :]) => `(Ty.union [: #inl $a :] [: #inr $b :])
  | `([: $a & $b :]) => `(Ty.inter [: $a :] [: $b :])
  | `([: $a × $b :]) => `(Ty.inter [: .left $a :] [: .right $b :])
  | `([: ∀ $a :: $b ≤ $c . $d :]) => `(Ty.univ [: $a :] ([: $b :], [: $c :]) [: $d :])
  | `([: ∀ $a:slm . $b:slm :]) => `(Ty.univ [: $a :] ([: £$a :], [: ? :]) [: $b :] )
  | `([: ∃ $a :: $b ≤ $c . $d  :]) => `(Ty.exis [: $a :] ([: $b :], [: $c :]) [: $d :])
  | `([: ∃ $a:slm . $b:slm :]) => `(Ty.exis [: $a :] ([: £$a :], [: ? :]) [: $b :] )
  | `([: μ 1 . $a :]) => `(Ty.recur [: $a :])
  | `([: ν 1 . $a :]) => `(Ty.corec [: $a :])

-- generic
  | `([: ($a) :]) => `([: $a :])

--escape 
  | `([: ⟨ $e ⟩ :]) => pure e

#eval [: 
    ∃ 2 :: .l £0 & .r £1 ≤ £3 .
      .l #succ £0 & .r #cons £1  |
    (∃ 2 :: .l £0 & .r £1 ≤ £3 .
      .l #succ £0 & .r #cons £1)
:]

#check [: £0 | ? :]
#check [: £0 & ? :]
#check [: £0 × ? :]
#check [: £0 + ? :]
def x := 0
#check [: ∀ 1 :: £0 ≤ ? . £⟨x⟩ :]
#check [: ∀ 1 :: £0 ≤ ? . £0 :]
#check [: ∀ 2 :: ? ≤ ? . £0 :]
#check [: ∀ 2 . £0 :]
#check [: ♢ :]
#check [: @24 :]
#check [: #foo ♢ | #boo ♢ :]
#check [: μ 1 . #foo £0 :]
#check [: μ 1 . #foo £0  & ? | @2 & ?:]
#check [: £3 & ? -> @1 | @2 :]
#check [: μ 1 . #foo £0 & ? | @2 & ? -> @1 | @2 :]
#check [: μ 1 . #foo £0 & ? | @2 & ? :]
#check [: ? :]



def lookup (key : Nat) : List (Nat × T) -> Option T
  | (k,v) :: bs => if key = k then some v else lookup key bs 
  | [] => none

def lookup_record (key : String) : List (String × T) -> Option T
  | (k,v) :: bs => if key = k then some v else lookup_record key bs 
  | [] => none

def liberate (i : Nat) : Nat -> List (Nat × Ty) 
  | 0 => []
  | n + 1 => (i, [: ? :]) :: (liberate (i + 1) n)

def refresh (i : Nat) (n : Nat) : (Nat × List Ty) := 
  let args := (List.range n).map (fun j => .fvar (i + j))
  let i' := i + n 
  (i', args)


-- partial def merge (op : T -> T -> T) (df : T) (env_ty1 : List (Nat × T))  (env_ty2 : List (Nat × T)) : List (Nat × T) :=
--   List.bind env_ty1 (fun (key₁, v₁) =>
--   List.bind env_ty2 (fun (key₂, v₂) =>
--     let uno := match lookup key₁ env_ty2 with
--       | some v₂ => [(key₁, op v₁ v₂)]
--       | none => [(key₁, op v₁ df)] 

--     let dos := match lookup key₂ env_ty1 with
--       | some _ => [] 
--       | none => [(key₂, op v₂ df)]
--     uno ++ dos
--   ))

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
cases_normal (#l₁ τ1) (#l₂ τ2) = true
cases_normal τ1 τ2 = 
  fmap (keys τ1) (ks₁ =>
  fmap (keys τ2) (ks₂ =>
    some (ks₁ = ks₂)
  )) = Some true
  (keys τ1) = (keys τ2) 
```


`decreasing τ τ = b`
```
decreasing (#l τ) τ = true 
decreasing τ1 τ2 =  
  any τ1 (.l τ => decreasing τ (project τ2 l)) andalso
  all τ1 (.l τ => ¬ increasing τ (project τ2 l))
```

`increasing τ τ = b`
```
increasing τ1 τ2 = decreasing τ2 τ1
```

`well_founded α τ = b`
```
well_founded α τ1 | τ2 = 
  cases_normal τ1 τ2 andalso
  well_founded α τ1 andalso
  well_founded α τ2

well_founded α ∀ env_ty ⟨τ' ⊆ α⟩ . τ = 
  α ∈ env_ty orelse
  decreasing τ τ' 
```
-/

def Ty.occurs (key : Nat)  : Ty -> Bool 
  | [: ? :] => false 
  | .bvar id => false 
  | .fvar id => key = id 
  | .unit => false 
  | .tag l ty => (Ty.occurs key ty) 
  | .field l ty => (Ty.occurs key ty)
  | [: ⟨ty1⟩ | ⟨ty2⟩ :] => (Ty.occurs key ty1) ∨ (Ty.occurs key ty2)
  -- | .union ty1 ty2 => (Ty.occurs key ty1) ∨ (Ty.occurs key ty2)
  | .inter ty1 ty2 => (Ty.occurs key ty1) ∨ (Ty.occurs key ty2)
  | .case ty1 ty2 => (Ty.occurs key ty1) ∨ (Ty.occurs key ty2)
  | .univ n (ty_c1, ty_c2) ty => (Ty.occurs key ty_c1) ∨ (Ty.occurs key ty_c2) ∨ (Ty.occurs key ty)
  | .exis n (ty_c1, ty_c2) ty => (Ty.occurs key ty_c1) ∨ (Ty.occurs key ty_c2) ∨ (Ty.occurs key ty)
  | .recur ty => (Ty.occurs key ty)
  | .corec ty => (Ty.occurs key ty)

def Ty.free_subst (m : List (Nat × Ty)) : Ty -> Ty
  | .dynamic => .dynamic 
  | .bvar id => .bvar id 
  | .fvar id => (match lookup id m with
    | some ty => ty 
    | none => .fvar id
  )
  | .unit => .unit
  | .tag l ty => .tag l (Ty.free_subst m ty) 
  | .field l ty => .field l (Ty.free_subst m ty)
  | .union ty1 ty2 => .union (Ty.free_subst m ty1) (Ty.free_subst m ty2)
  | .inter ty1 ty2 => .inter (Ty.free_subst m ty1) (Ty.free_subst m ty2)
  | .case ty1 ty2 => .case (Ty.free_subst m ty1) (Ty.free_subst m ty2)
  | .univ n (ty_c1, ty_c2) ty => (.univ
    n
    (Ty.free_subst m ty_c1, Ty.free_subst m ty_c2) 
    (Ty.free_subst m ty)
  )
  | .exis n (ty_c1, ty_c2) ty => (.exis
    n
    (Ty.free_subst m ty_c1, Ty.free_subst m ty_c2) 
    (Ty.free_subst m ty)
  )
  | .recur ty => .recur (Ty.free_subst m ty)
  | .corec ty => .corec (Ty.free_subst m ty)


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
  | .dynamic => .dynamic 
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
  | .tag l ty => .tag l (Ty.raise_binding start args ty) 
  | .field l ty => .field l (Ty.raise_binding start args ty)
  | .union ty1 ty2 => .union (Ty.raise_binding start args ty1) (Ty.raise_binding start args ty2)
  | .inter ty1 ty2 => .inter (Ty.raise_binding start args ty1) (Ty.raise_binding start args ty2)
  | .case ty1 ty2 => .case (Ty.raise_binding start args ty1) (Ty.raise_binding start args ty2)
  | .univ n (ty_c1, ty_c2) ty => (.univ
    n
    (Ty.raise_binding (start + n) args ty_c1, Ty.raise_binding (start + n) args ty_c2)
    (Ty.raise_binding (start + n) args ty)
  )
  | .exis n (ty_c1, ty_c2) ty => (.exis
    n
    (Ty.raise_binding (start + n) args ty_c1, Ty.raise_binding (start + n) args ty_c2)
    (Ty.raise_binding (start + n) args ty)
  )
  | .recur ty => .recur (Ty.raise_binding (start + 1) args ty)
  | .corec ty => .corec (Ty.raise_binding (start + 1) args ty)

syntax slm "↑" slm "/" slm : slm 

macro_rules
  | `([: $a ↑ $b / $c :]) => `(Ty.raise_binding [: $b :] [: $c :] [: $a :])


def τ := [: ? :]
#check [: ⟨τ⟩ ↑ 0 / [μ 1 . ⟨τ⟩]:]



/-
-- TODO: determine how to add co-recursive types (ν)  
-- TODO: pay attention to how recursive and co-recursive types are unrolled
-- ν and ∀ should be handled in similar ways. Don't unroll/raise until some application
  mandates a witness

---
recursive types

μ nat . #zero | #succ nat 

unroll

#zero | #succ (μ nat . #zero | #succ nat)

unroll on rhs of subtyping
can't unroll on lhs 

#zero | #succ #zero | #succ (μ nat . #zero | #succ nat)


---
co-recursive types

ν (nat -> list) . 
  #zero -> #nil & 
  #succ nat -> #cons (? × list)

desugar 

ν nat_to_list . 
  #zero -> #nil & 
  #succ nat -> #cons (? × list)
    &> (nat -> list) ≤ nat_to_list .

unroll on lhs of subtyping
can't unroll on rhs
-/


/-

-- specialization of existential vs universal
  -- existential on read is opaque.
  -- existential on write is specialized 
    -- (specialize if on rhs of subsumption)
  -- universial on read is specialized 
    -- (specialize if on lhs on subsumption)
  -- universal on write is opaque 

-/

partial def unroll : Ty -> Ty
  | .recur ty => 
    -- Ty.raise_binding 0 [Ty.recur τ] τ 
    [: ⟨ty⟩ ↑ 0 / [μ 1 . ⟨ty⟩]:]
  | .corec ty => 
    -- Ty.raise_binding 0 [Ty.recur τ] τ 
    [: ⟨ty⟩ ↑ 0 / [ν 1 . ⟨ty⟩]:]
  | ty => ty

def Ty.lower_binding (depth : Nat) : Ty -> Ty
  | .dynamic => .dynamic 
  | .bvar id => .bvar (id + depth)
  | .fvar id => .fvar id 
  | .unit => .unit
  | .tag l ty => .tag l (Ty.lower_binding depth ty) 
  | .field l ty => .field l (Ty.lower_binding depth ty)
  | .union ty1 ty2 => .union (Ty.lower_binding depth ty1) (Ty.lower_binding depth ty2)
  | .inter ty1 ty2 => .inter (Ty.lower_binding depth ty1) (Ty.lower_binding depth ty2)
  | .case ty1 ty2 => .case (Ty.lower_binding depth ty1) (Ty.lower_binding depth ty2)
  | .univ n (ty_c1, ty_c2) ty => (.univ
    n
    (Ty.lower_binding (depth + n) ty_c1, Ty.lower_binding (depth + n) ty_c2)
    (Ty.lower_binding (depth + n) ty)
  )
  | .exis n (ty_c1, ty_c2) ty => (.exis
    n
    (Ty.lower_binding (depth + n) ty_c1, Ty.lower_binding (depth + n) ty_c2)
    (Ty.lower_binding (depth + n) ty)
  )
  | .recur ty => .recur (Ty.lower_binding (depth + 1) ty)
  | .corec ty => .corec (Ty.lower_binding (depth + 1) ty)

syntax slm "↓" num : slm 

macro_rules
  | `([: $b:slm ↓ $a:num :]) => `(Ty.lower_binding $a [: $b :])


partial def roll_recur (key : Nat) (τ : Ty) : Ty :=
  if Ty.occurs key τ then
    [: (μ 1 . ⟨τ⟩↓1) % [⟨key⟩ / £0] :]
  else
    τ

partial def roll_corec (key : Nat) (τ : Ty) : Ty :=
  if Ty.occurs key τ then
    [: (ν 1 . ⟨τ⟩↓1) % [⟨key⟩ / £0] :]
  else
    τ

partial def Ty.equal (env_ty : List (Nat × Ty)) : Ty -> Ty -> Bool
  | .dynamic, .dynamic => true
  | .bvar id1, .bvar id2 => if id1 = id2 then true else false 
  | .fvar id1, .fvar id2 => if id1 = id2 then true else false
  | .unit, .unit => true
  | .tag l1 ty1, .tag l2 ty2 =>
    l1 = l2 ∧ (
      Ty.equal env_ty ty1 ty2 
    )
  | .field l1 ty1, .field l2 ty2 =>
    l1 = l2 ∧ (
      Ty.equal env_ty ty1 ty2 
    )

  | .union ty1 ty2, .union ty3 ty4 =>
    Ty.equal env_ty ty1 ty3 ∧
    Ty.equal env_ty ty2 ty4

  | .inter ty1 ty2, .inter ty3 ty4 =>
    Ty.equal env_ty ty1 ty3 ∧
    Ty.equal env_ty ty2 ty4

  | .case ty1 ty2, .case ty3 ty4 =>
    Ty.equal env_ty ty1 ty3 ∧
    Ty.equal env_ty ty2 ty4

  | .univ n1 (tyc1, tyc2) ty1, .univ n2 (tyc3, tyc4) ty2 =>
    n1 = n2 ∧
    Ty.equal env_ty tyc1 tyc3 ∧
    Ty.equal env_ty tyc2 tyc4 ∧
    Ty.equal env_ty ty1 ty2

  | .exis n1 (tyc1, tyc2) ty1, .exis n2 (tyc3, tyc4) ty2 =>
    n1 = n2 ∧
    Ty.equal env_ty tyc1 tyc3 ∧
    Ty.equal env_ty tyc2 tyc4 ∧
    Ty.equal env_ty ty1 ty2

  | .recur ty1, .recur ty2 =>
    Ty.equal env_ty ty1 ty2

  | .corec ty1, .corec ty2 =>
    Ty.equal env_ty ty1 ty2
  | _, _ => false

partial def Ty.resolve (env_ty : List (Nat × Ty)) : Ty -> Ty
  | .dynamic => Ty.dynamic  
  | .bvar id => Ty.bvar id  
  | .fvar id => match lookup id env_ty with
    | some ty => Ty.resolve env_ty ty 
    | none => .fvar id
  | .unit => .unit 
  | .tag l ty => Ty.tag l (Ty.resolve env_ty ty) 
  | .field l ty => Ty.field l (Ty.resolve env_ty ty) 
  | .union ty1 ty2 => Ty.union (Ty.resolve env_ty ty1) (Ty.resolve env_ty ty2)
  | .inter ty1 ty2 => Ty.inter (Ty.resolve env_ty ty1) (Ty.resolve env_ty ty2)
  | .case ty1 ty2 => Ty.case (Ty.resolve env_ty ty1) (Ty.resolve env_ty ty2)
  | .univ n (cty1, cty2) ty => 
      Ty.univ n  
        (Ty.resolve env_ty cty1, Ty.resolve env_ty cty2)
        (Ty.resolve env_ty ty)
  | .exis n (cty1, cty2) ty => 
      Ty.exis n  
        (Ty.resolve env_ty cty1, Ty.resolve env_ty cty2)
        (Ty.resolve env_ty ty)
  | .recur ty => Ty.recur (Ty.resolve env_ty ty)
  | .corec ty => Ty.corec (Ty.resolve env_ty ty)

def linearize_record : Ty -> Option Ty
  | .field l ty => 
    some (.field l ty)
  | .inter (.field l ty1) ty2 => 
    bind (linearize_record ty2) (fun linear_ty2 =>
      some (.inter (.field l ty1) linear_ty2)
    )
  | .inter ty1 (.field l ty2) => 
    bind (linearize_record ty1) (fun linear_ty1 =>
      some (.inter (.field l ty2) linear_ty1)
    )
  | _ => none

def linearize_fields : Ty -> Option (List (String × Ty))
  | .field l ty => some [(l, ty)]
  | .inter (.field l ty1) ty2 => 
    bind (linearize_fields ty2) (fun linear_ty2 =>
      (l, ty1) :: linear_ty2
    )
  | .inter ty1 (.field l ty2) => 
    bind (linearize_fields ty1) (fun linear_ty1 =>
      (l, ty2) :: linear_ty1
    )
  | _ => none

/-
(X ; Y) <: μ _

X <: (∃ α :: ((α ; Y) <: unroll (μ _)). α)
Y <: (∃ β :: ((X ; β) <: unroll (μ _)). β)
-/
def make_field_constraints (prev_ty : Ty) : Ty -> Ty -> List (Ty × Ty) 
  | (.field l ty1), mu_ty => 
      let ty2 := .exis 1 ( 
        (Ty.inter (Ty.lower_binding 1 prev_ty) (.field l (.bvar 0))),
        (Ty.lower_binding 1 (unroll mu_ty))
      ) (.bvar 0)
      [(ty1, ty2)]
  | .inter (.field l ty1) rem_ty, mu_ty => 
      let ty2 := 
      [: ∃ 1 :: (⟨prev_ty⟩↓1 & (#⟨l⟩ £0) & ⟨rem_ty⟩↓1) ≤ ⟨unroll mu_ty⟩↓1 . £0 :]

      let rem := make_field_constraints (Ty.inter prev_ty (.field l ty1)) rem_ty mu_ty
      if rem.length = 0 then
        []
      else 
        (ty1, ty2) :: rem
  | _, _ => [] 



partial def unify (i : Nat) (env_ty : List (Nat × Ty)) : 
Ty -> Ty -> Option (Nat × List (Nat × Ty))
  | .bvar id1, .bvar id2  =>
    if id1 = id2 then 
      some (i, [])
    else
      none

  | .unit, .unit => some (i, []) 

  | .tag l' ty', .tag l ty =>
    if l' = l then
      unify i env_ty ty' ty
    else
      none

  | .field l' ty', .field l ty =>
    if l' = l then
      unify i env_ty ty' ty
    else
      none

  | .case ty1 ty2', .case ty1' ty2 =>
    bind (unify i env_ty ty1' ty1) (fun (i, env_ty1) => 
    bind (unify i (env_ty1 ++ env_ty) ty2' ty2) (fun (i, env_ty2) =>
      some (i, env_ty2 ++ env_ty1)
    ))

  | ty', .exis n (ty_c1, ty_c2) ty =>
    let (i, args) := refresh i n 
    let ty_c1 := Ty.raise_binding 0 args ty_c1
    let ty_c2 := Ty.raise_binding 0 args ty_c2
    let ty := Ty.raise_binding 0 args ty
    bind (unify i env_ty ty_c1 ty_c2) (fun (i, env_ty1) =>
    bind (unify i (env_ty1 ++ env_ty) ty' ty) (fun (i, env_ty2) => 
      some (i, env_ty2 ++ env_ty1)
    ))
    -- list[{x;z}] <: ∃ X :: (X <: {x}) . list[X]
    -- X := {x} & Y |- list[{x;z}] <: list[X]
    -- X := {x} & Y |- list[{x;z}] <: list[{x} & Y]
    -- |- {x;z} <: {x} & Y
    -- Y := {z} | ⊥


  | .univ n (ty_c1, ty_c2) ty', ty =>
    let (i, args) := refresh i n 
    let ty_c1 := Ty.raise_binding 0 args ty_c1
    let ty_c2 := Ty.raise_binding 0 args ty_c2
    let ty' := Ty.raise_binding 0 args ty'
    bind (unify i env_ty ty_c1 ty_c2) (fun (i, env_ty1) =>
    bind (unify i (env_ty1 ++ env_ty) ty' ty) (fun (i, env_ty2) => 
      some (i, env_ty2 ++ env_ty1)
    ))

  | ty', .fvar id  => match lookup id env_ty with 
    | none => some (i + 1, [
        (id, .union (roll_corec id ty') (Ty.fvar i)),
        (id + 1, Ty.dynamic)
      ]) 
    | some ty => unify i env_ty ty' ty 

  | .fvar id, ty  => match lookup id env_ty with 
    | none => some (i + 1, [
        (id, .inter (roll_recur id ty) (Ty.fvar i)),
        (i, Ty.dynamic)
      ]) 
    | some ty' => unify i env_ty ty' ty 


  | .exis n (ty_c1, ty_c2) ty', ty =>
    if Ty.equal env_ty (.exis n (ty_c1, ty_c2) ty') ty then
      some (i, []) 
    else
      none

  | ty', .univ n (ty_c1, ty_c2) ty =>
    if Ty.equal env_ty ty' (.univ n (ty_c1, ty_c2) ty) then
      some (i, [])
    else
      none

  | .dynamic, _ => some (i, []) 
  | _, .dynamic => some (i, []) 


  | .recur ty', .recur ty =>
    if Ty.equal env_ty ty' ty then
      some (i, [])
    else
      let ty' := [: ⟨ty'⟩ ↑ 0 / [?]:]
      let ty := [: ⟨ty⟩ ↑ 0 / [?]:]
      unify i env_ty ty' ty

  | .tag l ty', .recur ty =>
    unify i env_ty (.tag l ty') (unroll (.recur ty))


  | ty', .recur ty =>
    bind (linearize_record (Ty.resolve env_ty ty')) (fun ty'' =>
    let cs := (make_field_constraints Ty.dynamic ty'' (Ty.recur ty))
    if cs.length = 0 then
      none
    else
      List.foldl (fun 
        | some (i, env_ty1), (ty_c1, ty_c2) => 
          bind (unify i env_ty ty_c1 ty_c2) (fun (i, env_ty2) =>
            some (i, env_ty2 ++ env_ty1)
          )
        | none, _ => none
      ) (some (i, [])) cs
    )


  | .corec ty', .corec ty =>
    if Ty.equal env_ty ty' ty then
      some (i, [])
    else
      let ty' := [: ⟨ty'⟩ ↑ 0 / [?] :]
      let ty := [: ⟨ty⟩ ↑ 0 / [?] :]
      unify i env_ty ty' ty


  | .corec ty_corec, Ty.case ty1 ty2 =>
    /-
    ν _ <: X -> Y 
    (∀ α :: (unroll(ν _) <: α -> Y) . α) <: X 
    (∀ β :: (unroll(ν _) <: X -> β) . β) <: Y
    -/
    let ty1'' := .univ 1 (Ty.lower_binding 1 (unroll (.corec ty_corec)), .case (Ty.bvar 0) ty2) (Ty.bvar 0) 
    let ty2'' := .univ 1 (Ty.lower_binding 1 (unroll (.corec ty_corec)), .case ty1 (Ty.bvar 0)) (Ty.bvar 0) 
    bind (unify i env_ty ty1'' ty1 ) (fun (i, env_ty1) =>
    bind (unify i env_ty ty2'' ty2 ) (fun (i, env_ty2) =>
      some (i, env_ty2 ++ env_ty1)
    ))


  | .union ty1 ty2, ty => 
    bind (unify i env_ty ty1 ty) (fun (i, env_ty1) => 
    bind (unify i (env_ty1 ++ env_ty) ty2 ty) (fun (i, env_ty2) =>
      some (i, env_ty2 ++ env_ty1)
    ))
    -- list[{x;y}] | list[{x;z}] <: list[X]
    -- list[{x;y}] <: list[X]
    -- X := {x;y} | Y |- list[{x;z}] <: list[X]
    -- list[{x;z}] <: list[{x;y} | Y]

  | ty, .union ty1 ty2 => 
    match unify i env_ty ty ty1 with
      | .none => unify i env_ty ty ty2
      | .some (i, env_ty1) =>
        match (unify i (env_ty1 ++ env_ty) ty ty2) with
          | .none => some (i, env_ty1)
          | .some (i, env_ty2) => some (i, env_ty2 ++ env_ty1)


  | ty, .inter ty1 ty2 => 
    bind (unify i env_ty ty ty1) (fun (i, env_ty1) => 
    bind (unify i (env_ty1 ++ env_ty) ty ty2) (fun (i, env_ty2) =>
      some (i, env_ty2 ++ env_ty1)
    ))

  | .inter ty1 ty2, ty => 
    match (unify i env_ty ty1 ty) with
      | .none => (unify i env_ty ty2 ty)
      | .some (i, env_ty1) => 
        match (unify i (env_ty1 ++ env_ty) ty2 ty) with
          | .none => (i, env_ty1)
          | .some (i, env_ty2) => some (i, env_ty2 ++ env_ty1)

  | _, _ => none


def zero_ := [: 
    #zero ♢
:]

#eval unify 3 [] [:
    (#dumb ♢)
:] zero_

#eval unify 3 [] [:
    (#zero ♢)
:] zero_

/-
  μ nat .
    #zero ♢ | 
    #succ nat 
-/
def nat_ := [: 
  μ 1 . 
    #zero ♢ |
    #succ £0
:]
#eval nat_

#eval unify 3 [] [:
    (#zero ♢)
:] nat_ 

#eval unify 3 [] [:
    (#succ (#zero ♢))
:] nat_ 

#eval unify 3 [] [:
    (#succ (@0))
:] nat_ 

def nat_list := [: 
  μ 1 .
    .l #zero ♢ & .r #nil ♢ |
    ∃ 2 :: .l £0 & .r £1 ≤ £2 .
      .l #succ £0 & .r #cons £1
:]

#eval Ty.raise_binding 0 [[:@33:], [:@44:]] [: .l #succ £0 & .r #cons £1 :]

#eval nat_list

#eval (unroll nat_list)

#eval [: (.l #succ #zero ♢ & .r #cons #nil ♢) :]

#eval unify 3 [] 
  [: (.l #zero ♢ & .r #nil ♢) :] 
  nat_list

#eval (linearize_record [: (.l #zero ♢ & .r #nil ♢) :])
#eval (Ty.resolve [] [: (.l #zero ♢ & .r #nil ♢) :])
#eval linearize_record (Ty.resolve [] [: (.l #zero ♢ & .r #nil ♢) :])
#eval make_field_constraints Ty.dynamic [: (.l #zero ♢ & .r #nil ♢) :] nat_list

#eval unify 3 [] 
  [: #zero ♢ :] 
  [: ∃ 1 :: (? & .l £0 & .r #nil ♢) ≤ ⟨Ty.lower_binding 1 (unroll nat_list)⟩ . £0 :]

#eval unify 3 [] 
  [: #zero ♢ :] 
  [: ∃ 1 :: (.l £0 & .r #nil ♢) ≤ ⟨Ty.lower_binding 1 (unroll nat_list)⟩ . £0 :]

#eval unify 3 [] 
  [: @0 :] 
  [: ∃ 1 :: (.l £0 & .r #nil ♢) ≤ ⟨Ty.lower_binding 1 (unroll nat_list)⟩ . £0 :]

#eval unify 3 [] 
  [: ∀ 1 :: (? & .l £0 & .r #nil ♢) ≤ ⟨Ty.lower_binding 1 (unroll nat_list)⟩ . £0 :]
  [: #zero ♢ :] 

#eval unify 3 [] 
  [: ∀ 1 :: (.l £0 & .r #nil ♢) ≤ ⟨Ty.lower_binding 1 (unroll nat_list)⟩ . £0 :]
  [: #zero ♢ :] 

#eval unify 3 [] 
  [: ∀ 1 :: (.l £0 & .r #nil ♢) ≤ ⟨Ty.lower_binding 1 (unroll nat_list)⟩ . £0 :]
  [: @0 :] 

#eval unify 3 [] 
  [: (.l #zero ♢ & .r @0) :] 
  nat_list

-- TODO: why does this terminate?
#eval unify 3 [] 
  [: (.l @0 & .r @1) :] 
  nat_list

#eval unify 3 [] 
  [: @0 :] 
  [: ∃ 1 :: (.l £0 & .r @1) ≤ ⟨Ty.lower_binding 1 (unroll nat_list)⟩ . £0 :]

#eval unroll nat_list 
#eval unify 3 [] 
  [: (.l @2 & .r @1) :] 
  (unroll nat_list)

#eval unify 3 [] 
  [: ∀ 1 :: (.l £0 & .r #nil ♢) ≤ ⟨Ty.lower_binding 1 (unroll nat_list)⟩ . £0 :]
  [: @0 :] 

#eval unify 3 [] [:
    (.l (#zero ♢ & £1) & .r #nil ♢)
:] (Ty.lower_binding 1 (unroll nat_list))

#eval unify 3 [] [:
    (.l (#zero ♢ | £1) & .r #nil ♢)
:] (Ty.lower_binding 1 (unroll nat_list))

#eval unify 3 [] [:
    (#zero ♢ | £1)
:] [: #zero ♢ :] 

#eval unify 3 [] [:
    (#zero ♢ & £1)
:] [: #zero ♢ :] 

-- expected: some
#eval unify 3 [] [:
    (.l #succ #zero ♢ & .r #cons #nil ♢)
:] nat_list 

#eval unify 3 [] [:
    (.l #zero ♢ & .r #dumb ♢)
:] nat_list 

#eval unify 3 [] 
  [: #dumb ♢ :] 
  [: ∃ 1 :: (.l #zero ♢ & .r £0 ) ≤ ⟨Ty.lower_binding 1 (unroll nat_list)⟩. £0:]

#eval unify 3 [] 
  [: #nil ♢ :] 
  [: ∃ 1 :: (.l #zero ♢ & .r £0 ) ≤ ⟨Ty.lower_binding 1 (unroll nat_list)⟩. £0:]

#eval unify 3 [] 
  [: ∀ 1 :: (.l #zero ♢ & .r £0 ) ≤ ⟨Ty.lower_binding 1 (unroll nat_list)⟩. £0:]
  [: #dumb ♢ :] 

-- expeeted: some (@0 ↦ #nil ♢) 
#eval unify 3 [] 
  [: (.l #zero ♢ & .r @0) :] 
  nat_list

#eval bind (unify 3 [] 
  [: (.l #zero ♢ & .r @0) :] 
  nat_list) (fun (i, env_ty) =>
    some (Ty.resolve env_ty [: @0 :])
  )

#eval [: ∃ 1 :: (.l  #zero ♢ & .r £0) ≤ @55 . £0 :]
#eval Ty.raise_binding 0 [ [:@0:] ] [: ∃ 1 :: (.l  #zero ♢ & .r £0) ≤ @55 . £0 :]
#eval Ty.raise_binding 0 [ [:@0:] ] [: (.l  #zero ♢ & .r £0) :]
#eval Ty.raise_binding 0 [ [:@0:] ] [: £0 :]

#eval Ty.raise_binding 0 [ [:@0:] ] [: ⟨Ty.lower_binding 1 (unroll nat_list)⟩ :]
#eval (unroll nat_list)

#eval [: ⟨Ty.lower_binding 1 (unroll nat_list)⟩ :]
#eval [: ∃ 1 :: (.l  #zero ♢ & .r £0) ≤ ⟨Ty.lower_binding 1 (unroll nat_list)⟩ . £0 :]
#eval unify 3 [] 
  [: @0 :] 
  [: ∃ 1 :: (.l  #zero ♢ & .r £0) ≤ ⟨Ty.lower_binding 1 (unroll nat_list)⟩ . £0 :]

#eval unify 3 [] 
  [: (.l  #zero ♢ & .r @0) :] 
  [:  ⟨Ty.lower_binding 1 (unroll nat_list)⟩ :]


#eval unify 3 [] 
  [: ∀ 1 :: (.l  #zero ♢ & .r £0) ≤ ⟨Ty.lower_binding 1 (unroll nat_list)⟩ . £0 :]
  [: @0 :] 

#eval unify 3 [] [:
    (.l #zero ♢ & .r @0)
:] (unroll nat_list) 

#eval unify 3 [] [:
    (.l #succ #zero ♢ & .r #cons @0)
:] nat_list 

#eval unify 3 [] 
  [: #cons @0 :] 
  [: ∃ 1 :: (.l #succ #zero ♢ & .r £0) ≤ ⟨Ty.lower_binding 1 (unroll nat_list)⟩ . £0 :]

#eval unify 3 [] 
  [: #cons ♢ :] 
  [: ∃ 1 :: (.l #succ #zero ♢ & .r £0) ≤ ⟨Ty.lower_binding 1 (unroll nat_list)⟩ . £0 :]

#eval unify 3 [] 
  [: #cons #nil ♢ :] 
  [: ∃ 1 :: (.l #succ #zero ♢ & .r £0) ≤ ⟨Ty.lower_binding 1 (unroll nat_list)⟩ . £0 :]

#eval unify 3 [] 
  [: ∀ 1 :: (.l #succ #zero ♢ & .r £0) ≤ ⟨Ty.lower_binding 1 (unroll nat_list)⟩ . £0 :]
  [: #cons @0 :] 

#eval unify 3 [] 
  [: (.l #succ #zero ♢ & .r #cons @0) :] 
  [: ⟨unroll nat_list⟩ :]

#eval unify 3 [] [:
    (.l (#succ @0) & .r #cons #nil ♢)
:] nat_list 

#eval unify 3 [] [:
    (.l @0 & .r @1)
:] nat_list 

#eval make_field_constraints Ty.dynamic [: (.l @0 & .r @1) :] nat_list


def exi_ := [: 
  ∃ 1 .  #succ £0
:]

#eval unify 3 [] [:
    (#succ (#zero ♢))
:] exi_ 

def free_ := [: 
  #succ @0
:]

#eval unify 3 [] [:
    (#succ (#zero ♢))
:] free_ 

def dynamic_ := [: 
  #succ ? 
:]

#eval unify 3 [] [:
    (#succ (#zero ♢))
:] dynamic_ 


/-
  μ plus .
    #zero ♢ × #zero ♢ × #zero ♢ | 

    ∃ N :: #zero , N, N ≤ plus .  
      #zero ♢ × #succ N × #succ N | 

    ∃ X Y Z :: X, Y, Z ≤ plus .  
      #succ X × Y × #succ Z
-/
def plus := [: 
  μ 1 . 
    (.x #zero ♢ & .y #zero ♢ & .z #zero ♢) |

    (∃ 1 :: (.x #zero ♢ & .y £0 & .z £0) ≤ £1 .   
      (.x #zero ♢ & .y #succ £0 & .z #succ £0)) |

    (∃ 3 :: (.x £0 & .y £1 & .z £2) ≤ £3 .   
      (.x #succ £0 & .y £1 & .z #succ £2))
:]

#print plus

#eval [: (.x #zero ♢ & .y #zero ♢ & .z #zero ♢) :]  
#eval [: #succ #succ #zero ♢ :]  


#eval unify 3 [] [:
    .x #zero ♢ &
    .y @0 &
    .z #zero ♢
:] plus

#eval unify 3 [] [:
  (
    .x #zero ♢ &
    .y @0 &
    .z #succ #succ #zero ♢
  )
:] plus

#eval unify 3 [] [:
  (
    .x (#succ #zero ♢) &
    .y (@0) &
    .z (#succ (#succ #succ (#zero ♢)))
  )
:] plus

#eval unify 3 [] [:
  (
    .x (#succ #zero ♢) &
    .y (#succ #zero ♢) &
    .z (@0)
  )
:] plus


/-
t ::=                             term
  _                               hole 
  x                               variable
  ()                              unit
  #l t                            tag
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

env_tm ::=                             typing environment 
  ⬝                                empty
  x : τ :: env_tm                      extension

-/

inductive Tm : Type
  | hole : Tm 
  | bvar : Nat -> Tm 
  | fvar : Nat -> Tm 
  | unit : Tm
  | tag : String -> Tm -> Tm
  | record : List (String × Tm) -> Tm
  | func : List (Nat × Tm × Ty × Tm) -> Tm
  | proj : Tm -> String -> Tm
  | app : Tm -> Tm -> Tm
  | letb : Ty -> Tm -> Tm -> Tm
  | fix : Tm -> Tm


-- NOTE: there is no need to instantiate in infer. All that jazz happens in subtype/unify
-- the assymetry of subtyping makes it clear when to instantiate/raise/free a variable
-- and when to unroll a looping type

-- notation convetion:
  -- prime tick marks for updated versions
  -- numbers for new parts
  -- no subscripts
  -- no greek
  -- general to specific, 
    -- e.g. env_ty, (not ty_env)
    -- e.g. ty_recur, (not mu_ty)


partial def patvars (env_tm : List (Nat × Ty)): Tm -> Ty -> Option (List (Nat × Ty))
  | Tm.fvar id, ty =>
    match lookup id env_tm with
      | some _ => none 
      | none => [(id, ty)] 
  | .tag l_tm tm, .tag l_ty ty => 
    if l_tm = l_ty then
      patvars env_tm tm ty 
    else none
  | .record fds, ty  => 
    bind (linearize_fields ty) (fun linear_ty =>
      if linear_ty.length = fds.length then
        List.foldl (fun acc => fun (l, tm)  =>
          bind acc (fun env_tm_1 =>
          bind (lookup_record l linear_ty) (fun ty =>
          bind (patvars (env_tm_1 ++ env_tm) tm ty) (fun env_tm_2 =>
            some (env_tm_2 ++ env_tm_1)
          )))
        ) (some []) fds
      else
        none
    )
  -- TODO: finish
  | _, _ => none


def Ty.dynamic_subst (i : Nat) : Ty -> Nat × Ty
  | .dynamic => 
    (i + 1, .fvar i) 
  | .bvar id => (i, .bvar id)
  | .fvar id => (i, .fvar id)
  | .unit => (i, .unit)
  | .tag l ty => 
    let (i, ty) := (Ty.dynamic_subst i ty)
    (i, .tag l ty) 
  | .field l ty => 
    let (i, ty) := Ty.dynamic_subst i ty
    (i, .field l ty) 
  | .union ty1 ty2 => 
      let (i, ty1) := (Ty.dynamic_subst i ty1)
      let (i, ty2) := (Ty.dynamic_subst i ty2)
      (i, .union ty1 ty2)
  | .inter ty1 ty2 => 
      let (i, ty1) := (Ty.dynamic_subst i ty1)
      let (i, ty2) := (Ty.dynamic_subst i ty2)
      (i, .inter ty1 ty2)
  | .case ty1 ty2 => 
      let (i, ty1) := (Ty.dynamic_subst i ty1)
      let (i, ty2) := (Ty.dynamic_subst i ty2)
      (i, .case ty1 ty2)
  | .univ n (ty_c1, ty_c2) ty => 
    let (i, ty_c1) := Ty.dynamic_subst i ty_c1
    let (i, ty_c2) := Ty.dynamic_subst i ty_c2
    let (i, ty) := (Ty.dynamic_subst i ty)
    (i, .univ n (ty_c1, ty_c2) ty)
  | .exis n (ty_c1, ty_c2) ty => 
    let (i, ty_c1) := Ty.dynamic_subst i ty_c1
    let (i, ty_c2) := Ty.dynamic_subst i ty_c2
    let (i, ty) := (Ty.dynamic_subst i ty)
    (i, .exis n (ty_c1, ty_c2) ty)
  | .recur ty => 
    let (i, ty) := Ty.dynamic_subst i ty
    (i, .recur ty)
  | .corec ty => 
    let (i, ty) := Ty.dynamic_subst i ty
    (i, .corec ty)

/-
NOTE: infer returns a refined type in addition the type variable assignments
assignments alone do not refine enough due to subtyping
NOTE: deconstructing types is reduced to unification 
-/
partial def infer 
  (i : Nat)
  (env_ty : List (Nat × Ty)) (env_tm : List (Nat × Ty)) (t : Tm) (ty : Ty) : 
  Option (Nat × List (Nat × Ty) × Ty) := match t with
  | .unit => bind (unify i env_ty Ty.unit ty) (fun (i, env_ty) =>
      (i, env_ty, Ty.unit)
    )
  | .bvar _ => none
  | .fvar id =>
    bind (lookup id env_tm) (fun ty' =>
      let (i, ty_x, env_ty_x) := (i + 1, .fvar i, [(i, ty')])
      bind (unify i (env_ty_x ++ env_ty) ty_x ty) (fun (i, env_ty1) =>
        some (i, env_ty1 ++ env_ty_x, ty_x)
      )
    ) 

  | .tag l t1 =>   
    let (i, ty1) := (i + 1, .fvar i) 
    bind (unify i (env_ty) (.tag l ty1) ty) (fun (i, env_ty1) =>
    bind (infer i (env_ty1 ++ env_ty) env_tm t1 ty1) (fun (i, env_ty2, ty1') =>
      some (i, env_ty2 ++ env_ty1, .tag l ty1')
    ))

  | .record [] => none

  | .record ((l, t1) :: .nil) =>
    let (i, ty1) := (i + 1, .fvar i) 
    bind (unify i (env_ty) (.tag l ty1) ty) (fun (i, env_ty1) =>
    bind (infer i (env_ty1 ++ env_ty) env_tm t1 ty1) (fun (i, env_ty2, ty1') =>
      some (i, env_ty2 ++ env_ty1, .tag l ty1')
    ))

  | .record (fd :: fds) =>
    let (i, ty_fd) := (i + 1, Ty.fvar i) 
    let (i, ty_fds) := (i + 1, Ty.fvar i) 
    bind (unify i env_ty (Ty.inter ty_fd ty_fds) ty) (fun (i, env_ty1) => 
    bind (infer i (env_ty1 ++ env_ty) env_tm (.record fds) ty_fds) (fun (i, env_ty_fds, ty_fds') =>
    bind (infer i (env_ty1 ++ env_ty) env_tm (.record [fd]) ty_fd) (fun (i, env_ty_fd, ty_fd') =>
      some (i, env_ty_fd ++ env_ty_fds ++ env_ty1, .inter ty_fd' ty_fds')
    )))
  
  | .func [] => none
  | .func ((n, p, ty_p, b) :: .nil) => 
    let (i, ty_p) := Ty.dynamic_subst i ty_p 
    let (i, ty_b) := (i + 1, .fvar i)
    bind (patvars env_tm p ty_p) (fun env_tm1 =>
      if env_tm1.length = n then
        bind (unify i (env_ty) (.case ty_p ty_b) ty) (fun (i, env_ty1) =>
        bind (infer i (env_ty1 ++ env_ty) (env_tm1 ++ env_tm) b ty_b) (fun (i, env_ty2, ty_b') =>
          some (i, env_ty2 ++ env_ty1, Ty.case ty_p ty_b')
        ))
      else none
    )

  | .func (f :: fs) =>
    let (i, ty_f) := (i + 1, Ty.fvar i) 
    let (i, ty_fs) := (i + 1, Ty.fvar i) 
    bind (unify i env_ty (Ty.inter ty_f ty_fs) ty) (fun (i, env_ty1) => 
    bind (infer i (env_ty1 ++ env_ty) env_tm (.func fs) ty_fs) (fun (i, env_ty_fs, ty_fs') =>
    bind (infer i (env_ty1 ++ env_ty) env_tm (.func [f]) ty_f) (fun (i, env_ty_f, ty_f') =>
      some (i, env_ty_f ++ env_ty_fs, .inter ty_f' ty_fs')
    )))

  | .proj t1 l =>
    let (i, ty') := (i + 1, Ty.fvar i)
    bind (infer i env_ty env_tm t1 (Ty.field l ty)) (fun (i, env_ty1, ty1) =>
    bind (unify i (env_ty1 ++ env_ty) ty1 (Ty.field l ty')) (fun (i, env_ty2) =>
      some (i, env_ty2 ++ env_ty1, ty')
    ))

    -- bind (linearize_fields ty1) (fun list_field =>
    -- bind (lookup_record l list_field) (fun ty' =>

  | .app t2 t1 =>
    let (i, ty') := (i + 1, Ty.fvar i)
    let (i, ty1) := (i + 1, Ty.fvar i)
    bind (infer i (env_ty) env_tm t2 (Ty.case .dynamic ty)) (fun (i, env_ty1, ty2) =>
    -- ty2 = ty1 -> ty'
    bind (unify i (env_ty1 ++ env_ty) ty2 (.case ty1 ty')) (fun (i, env_ty2) =>
    bind (infer i (env_ty2 ++ env_ty1 ++ env_ty) env_tm t1 ty1) (fun (i, env_ty3, ty1') =>
    bind (unify i (env_ty3 ++ env_ty2 ++ env_ty1 ++ env_ty) ty2 (Ty.case ty1' ty)) (fun (i, env_ty4) =>
      some (i, env_ty4 ++ env_ty3 ++ env_ty2  ++ env_ty1 , ty')
    ))))

  | .letb ty1 t1 t => 
    let (i, ty1) := Ty.dynamic_subst i ty1
    let (i, env_tmx) := (i + 1, [(i, Ty.univ 1 (Ty.bvar 0, ty1) (Ty.bvar 0))]) 
    bind (infer i (env_ty) env_tm t1 ty1) (fun (i, env_ty1, _) =>
    bind (infer i (env_ty1 ++ env_ty) (env_tmx ++ env_tm) t ty) (fun (i, env_ty2, ty') =>
      some (i, env_ty2 ++ env_ty1, ty')
    ))


  | .fix t1 =>
    let (i, ty') := (i + 1, Ty.fvar i)
    bind (infer i env_ty env_tm t1 (Ty.case ty ty)) (fun (i, env_ty1, ty1') =>
    bind (unify i (env_ty1 ++ env_ty) ty1' (.case ty' ty')) (fun (i, env_ty2) =>
      some (i, env_ty2 ++ env_ty1, ty')
    ))
    /-
      (λ x => fix (λ self =>  
        λ #zero () => #nil () ;  
        λ #succ n => #cons (x, self n)
      ))
      
      (α -> ( 
        #zero ♢ -> #nil ♢ &
        ∀ N L :: α <: (N -> L) .
          #succ N -> #cons (X × L)) 
      )) <: τ -> τ

      ( 
        #zero ♢ -> #nil ♢ &
        ∀ N L :: α <: (N -> L) .
          #succ N -> #cons (X × L)) 
      ) <: α 

      -- via roll_rec
      (ν α .  
        #zero ♢ -> #nil ♢ &
        ∀ N L :: α <: (N -> L) .
          #succ N -> #cons (X × L)) 
      )

      -- via sugar
      X -> ((ν (N -> L) . 
        #zero ♢ -> #nil  ♢ &
        #succ N -> #cons (X × L)) 
      )

    -/

  | _ => none

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
  - combine intersection (i.e. &) with dynamic type (i.e. ?)
- lenient
  - maintain bottom actual type
  - τ & ? = τ & ⊥ = ⊥
- strict
  - narrow dynamic expected type from known expected type
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
  - combine union (i.e. |) with dynamic type (i.e. ?)
- lenient
  - maintain top expected type 
  - τ | ? = τ | ⊤ = ⊤ 
- strict
  - widen dynamic actual type from known actual type
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


### tags induction type
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

- the dynamic type (i.e. ?) has special consistent subtyping semantics
  - behaves like a bottom type for actual types
  - behaves like a top type for expected types

- the singleton type (e.g. #l []) corresponds to a single literal term
-/

/-
- consider adding relative complement type 
  - i.e. binary negation type operator
  - i.e. (τ1 \ τ2) ⊆ (τ1 & ¬ τ2), where ⊤ / τ2 = ¬ τ2)
-/
