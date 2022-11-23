-- TODO: look into widening in abstract interpretation

inductive Ty : Type
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
  | `([: $a -> $b :]) => `(Ty.case [: $a :] [: $b :])
  | `([: $a | $b :]) => `(Ty.union [: $a :] [: $b :])
  | `([: $a + $b :]) => `(Ty.union [: #inl $a :] [: #inr $b :])
  | `([: $a & $b :]) => `(Ty.inter [: $a :] [: $b :])
  | `([: $a × $b :]) => `(Ty.inter [: .left $a :] [: .right $b :])
  | `([: ∀ $a :: $b ≤ $c . $d :]) => `(Ty.univ [: $a :] ([: $b :], [: $c :]) [: $d :])
  | `([: ∀ $a:slm . $b:slm :]) => `(Ty.univ [: $a :] ([: £$a :], [: £$a :]) [: $b :] )
  | `([: ∃ $a :: $b ≤ $c . $d  :]) => `(Ty.exis [: $a :] ([: $b :], [: $c :]) [: $d :])
  | `([: ∃ $a:slm . $b:slm :]) => `(Ty.exis [: $a :] ([: £$a :], [: £$a :]) [: $b :] )
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

#check [: £0 | @0 :]
#check [: £0 & @0 :]
#check [: £0 × @0 :]
#check [: £0 + @0 :]
def x := 0
#check [: ∀ 1 :: £0 ≤ @0 . £⟨x⟩ :]
#check [: ∀ 1 :: £0 ≤ @0 . £0 :]
#check [: ∀ 2 :: @0 ≤ @0 . £0 :]
#check [: ∀ 2 . £0 :]
#check [: ♢ :]
#check [: @24 :]
#check [: #foo ♢ | #boo ♢ :]
#check [: μ 1 . #foo £0 :]
#check [: μ 1 . #foo £0  & @0 | @2 & @0:]
#check [: £3 & @0 -> @1 | @2 :]
#check [: μ 1 . #foo £0 & @0 | @2 & @0 -> @1 | @2 :]
#check [: μ 1 . #foo £0 & @0 | @2 & @0 :]
#check [: @0 :]



def lookup (key : Nat) : List (Nat × T) -> Option T
  | (k,v) :: bs => if key = k then some v else lookup key bs 
  | [] => none

def lookup_record (key : String) : List (String × T) -> Option T
  | (k,v) :: bs => if key = k then some v else lookup_record key bs 
  | [] => none

-- def liberate (i : Nat) : Nat -> List (Nat × Ty) 
--   | 0 => []
--   | n + 1 => (i, [: ? :]) :: (liberate (i + 1) n)

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


-- #check [: (£1) % [1 / @0] :]
#check [: (£1) % [1/@0] :]

#check Fin

def Ty.raise_binding (start : Nat) (args : List Ty) : Ty -> Ty
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


def τ := [: @0 :]
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

-- def Ty.lower_binding (depth : Nat) : Ty -> Ty
--   | .bvar id => .bvar (id + depth)
--   | .fvar id => .fvar id 
--   | .unit => .unit
--   | .tag l ty => .tag l (Ty.lower_binding depth ty) 
--   | .field l ty => .field l (Ty.lower_binding depth ty)
--   | .union ty1 ty2 => .union (Ty.lower_binding depth ty1) (Ty.lower_binding depth ty2)
--   | .inter ty1 ty2 => .inter (Ty.lower_binding depth ty1) (Ty.lower_binding depth ty2)
--   | .case ty1 ty2 => .case (Ty.lower_binding depth ty1) (Ty.lower_binding depth ty2)
--   | .univ n (ty_c1, ty_c2) ty => (.univ
--     n
--     (Ty.lower_binding (depth + n) ty_c1, Ty.lower_binding (depth + n) ty_c2)
--     (Ty.lower_binding (depth + n) ty)
--   )
--   | .exis n (ty_c1, ty_c2) ty => (.exis
--     n
--     (Ty.lower_binding (depth + n) ty_c1, Ty.lower_binding (depth + n) ty_c2)
--     (Ty.lower_binding (depth + n) ty)
--   )
--   | .recur ty => .recur (Ty.lower_binding (depth + 1) ty)
--   | .corec ty => .corec (Ty.lower_binding (depth + 1) ty)

-- syntax slm "↓" num : slm 

-- macro_rules
--   | `([: $b:slm ↓ $a:num :]) => `(Ty.lower_binding $a [: $b :])


partial def roll_recur (key : Nat) (τ : Ty) : Ty :=
  if Ty.occurs key τ then
    [: (μ 1 . ⟨τ⟩) % [⟨key⟩ / £0] :]
  else
    τ

partial def roll_corec (key : Nat) (τ : Ty) : Ty :=
  if Ty.occurs key τ then
    [: (ν 1 . ⟨τ⟩) % [⟨key⟩ / £0] :]
  else
    τ

partial def Ty.reduce (env_ty : List (Nat × Ty)) : Ty -> Ty
  | .bvar id => Ty.bvar id  
  | .fvar id => match lookup id env_ty with
    | some ty => Ty.reduce env_ty ty 
    | none => Ty.fvar id 
  | .unit => .unit 
  | .tag l ty => Ty.tag l (Ty.reduce env_ty ty) 
  | .field l ty => Ty.field l (Ty.reduce env_ty ty) 
  | .union ty1 ty2 => Ty.union (Ty.reduce env_ty ty1) (Ty.reduce env_ty ty2)
  | .inter ty1 ty2 => Ty.inter (Ty.reduce env_ty ty1) (Ty.reduce env_ty ty2)
  | .case ty1 ty2 => Ty.case (Ty.reduce env_ty ty1) (Ty.reduce env_ty ty2)
  | .univ n (cty1, cty2) ty => 
      Ty.univ n  
        (Ty.reduce env_ty cty1, Ty.reduce env_ty cty2)
        (Ty.reduce env_ty ty)
  | .exis n (cty1, cty2) ty => 
      Ty.exis n  
        (Ty.reduce env_ty cty1, Ty.reduce env_ty cty2)
        (Ty.reduce env_ty ty)
  | .recur ty => Ty.recur (Ty.reduce env_ty ty)
  | .corec ty => Ty.corec (Ty.reduce env_ty ty)


partial def Ty.equal_syntax : Ty -> Ty -> Bool
  | .bvar id1, .bvar id2 => if id1 = id2 then true else false 
  | .fvar id1, .fvar id2 => if id1 = id2 then true else false 
  | .unit, .unit => true
  | .tag l1 ty1, .tag l2 ty2 =>
    l1 = l2 ∧ (
      Ty.equal_syntax ty1 ty2 
    )
  | .field l1 ty1, .field l2 ty2 =>
    l1 = l2 ∧ (
      Ty.equal_syntax ty1 ty2 
    )

  | .union ty1 ty2, .union ty3 ty4 =>
    Ty.equal_syntax ty1 ty3 ∧
    Ty.equal_syntax ty2 ty4

  | .inter ty1 ty2, .inter ty3 ty4 =>
    Ty.equal_syntax ty1 ty3 ∧
    Ty.equal_syntax ty2 ty4

  | .case ty1 ty2, .case ty3 ty4 =>
    Ty.equal_syntax ty1 ty3 ∧
    Ty.equal_syntax ty2 ty4

  | .univ n1 (tyc1, tyc2) ty1, .univ n2 (tyc3, tyc4) ty2 =>
    n1 = n2 ∧
    Ty.equal_syntax tyc1 tyc3 ∧
    Ty.equal_syntax tyc2 tyc4 ∧
    Ty.equal_syntax ty1 ty2

  | .exis n1 (tyc1, tyc2) ty1, .exis n2 (tyc3, tyc4) ty2 =>
    n1 = n2 ∧
    Ty.equal_syntax tyc1 tyc3 ∧
    Ty.equal_syntax tyc2 tyc4 ∧
    Ty.equal_syntax ty1 ty2

  | .recur ty1, .recur ty2 =>
    Ty.equal_syntax ty1 ty2

  | .corec ty1, .corec ty2 =>
    Ty.equal_syntax ty1 ty2
  | _, _ => false

partial def Ty.equal (env_ty : List (Nat × Ty)) (ty1 : Ty) (ty2 : Ty) : Bool :=
  let ty1 := Ty.reduce env_ty ty1 
  let ty2 := Ty.reduce env_ty ty2 
  Ty.equal_syntax ty1 ty2 

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
        (Ty.inter (prev_ty) (.field l (.bvar 0))),
        ((unroll mu_ty))
      ) (.bvar 0)
      [(ty1, ty2)]
  | .inter (.field l ty1) rem_ty, mu_ty => 
      let ty2 := 
      [: ∃ 1 :: (⟨prev_ty⟩ & (#⟨l⟩ £0) & ⟨rem_ty⟩) ≤ ⟨unroll mu_ty⟩ . £0 :]

      let rem := make_field_constraints (Ty.inter prev_ty (.field l ty1)) rem_ty mu_ty
      if rem.length = 0 then
        []
      else 
        (ty1, ty2) :: rem
  | _, _ => [] 



/-

result:
empty list is failure
non-empty list represents the solutions of unification

-/
partial def unify (i : Nat) (env_ty : List (Nat × Ty)) : 
Ty -> Ty -> List (Nat × List (Nat × Ty))
  | .bvar id1, .bvar id2  =>
    if id1 = id2 then 
      [ (i, []) ]
    else
      .nil

  | .unit, .unit => [ (i, []) ] 

  | .tag l' ty', .tag l ty =>
    if l' = l then
      unify i env_ty ty' ty
    else
      .nil 

  | .field l' ty', .field l ty =>
    if l' = l then
      unify i env_ty ty' ty
    else
      .nil

  | .case ty1 ty2', .case ty1' ty2 =>
    List.bind (unify i env_ty ty1' ty1) (fun (i, env_ty1) => 
    List.bind (unify i (env_ty1 ++ env_ty) ty2' ty2) (fun (i, env_ty2) =>
      [ (i, env_ty2 ++ env_ty1) ]
    ))
    -- bind (unify i env_ty ty1' ty1) (fun (i, env_ty1) => 
    -- bind (unify i (env_ty1 ++ env_ty) ty2' ty2) (fun (i, env_ty2) =>
    --   some (i, env_ty2 ++ env_ty1)
    -- ))

  | ty', .fvar id  => match lookup id env_ty with 
    | none => [ (i + 1, [
        (id, .union (roll_corec id ty') (Ty.fvar i))
      ]) ]
    | some ty => unify i env_ty ty' ty 

  | .fvar id, ty  => match lookup id env_ty with 
    | none => [ (i + 1, [
        (id, .inter (roll_recur id ty) (Ty.fvar i))
      ]) ]
    | some ty' => unify i env_ty ty' ty 


  | ty', .exis n (ty_c1, ty_c2) ty =>
    let (i, args) := (i + n, (List.range n).map (fun j => .fvar (i + j)))

    let ty_c1 := Ty.raise_binding 0 args ty_c1
    let ty_c2 := Ty.raise_binding 0 args ty_c2
    let ty := Ty.raise_binding 0 args ty
    List.bind (unify i env_ty ty' ty) (fun (i, env_ty1) =>
    List.bind (unify i (env_ty1 ++ env_ty) ty_c1 ty_c2) (fun (i, env_ty2) => 
      [ (i, env_ty2 ++ env_ty1) ]
    ))
    -- )
    -- list[{x;z}] <: ∃ X :: (X <: {x}) . list[X]
    -- X := {x} & Y |- list[{x;z}] <: list[X]
    -- X := {x} & Y |- list[{x;z}] <: list[{x} & Y]
    -- |- {x;z} <: {x} & Y
    -- Y := {z} | ⊥


  | .univ n (ty_c1, ty_c2) ty', ty =>
    let (i, args) := (i + n, (List.range n).map (fun j => .fvar (i + j)))
    let ty_c1 := Ty.raise_binding 0 args ty_c1
    let ty_c2 := Ty.raise_binding 0 args ty_c2
    let ty' := Ty.raise_binding 0 args ty'
    List.bind (unify i env_ty ty' ty) (fun (i, env_ty1) =>
    List.bind (unify i (env_ty1 ++ env_ty) ty_c1 ty_c2) (fun (i, env_ty2) => 
      [ (i, env_ty2 ++ env_ty1) ]
    ))

  | .exis n (ty_c1, ty_c2) ty', ty =>
    if Ty.equal env_ty (.exis n (ty_c1, ty_c2) ty') ty then
      [ (i, [])  ]
    else
      .nil

  | ty', .univ n (ty_c1, ty_c2) ty =>
    if Ty.equal env_ty ty' (.univ n (ty_c1, ty_c2) ty) then
      [ (i, []) ]
    else
      .nil 

  | .recur ty', .recur ty =>
    if Ty.equal env_ty ty' ty then
      [ (i, []) ]
    else
      let ty' := [: ⟨ty'⟩ ↑ 0 / [μ 1 . ⟨ty⟩]:]
      let ty := [: ⟨ty⟩ ↑ 0 / [μ 1 . ⟨ty⟩]:]
      unify i env_ty ty' ty

  | .tag l ty', .recur ty =>
    unify i env_ty (.tag l ty') (unroll (.recur ty))


  | ty', .recur ty =>
    match linearize_record (Ty.reduce env_ty ty') with 
      | .some ty'' => unify i env_ty ty'' (unroll (Ty.recur ty))
      | .none => .nil

  | .corec ty', .corec ty =>
    if Ty.equal env_ty ty' ty then
      [ (i, []) ]
    else
      let ty' := [: ⟨ty'⟩ ↑ 0 / [μ 1 . ⟨ty'⟩] :]
      let ty := [: ⟨ty⟩ ↑ 0 / [μ 1 . ⟨ty'⟩] :]
      unify i env_ty ty' ty


  | .corec ty_corec, Ty.case ty1 ty2 =>
    unify i env_ty (unroll (Ty.corec ty_corec)) (Ty.case ty1 ty2)
    -- /-
    -- ν _ <: X -> Y 
    -- (∀ α :: (unroll(ν _) <: α -> Y) . α) <: X 
    -- (∀ β :: (unroll(ν _) <: X -> β) . β) <: Y
    -- -/
    -- let ty1' := .univ 1 ((unroll (.corec ty_corec)), .case (Ty.bvar 0) ty2) (Ty.bvar 0) 
    -- let ty2' := .univ 1 ((unroll (.corec ty_corec)), .case ty1 (Ty.bvar 0)) (Ty.bvar 0) 
    -- bind (unify i env_ty ty1' ty1 ) (fun (i, env_ty1) =>
    -- bind (unify i env_ty ty2' ty2 ) (fun (i, env_ty2) =>
    --   some (i, env_ty2 ++ env_ty1)
    -- ))


  | .union ty1 ty2, ty => 
    List.bind (unify i env_ty ty1 ty) (fun (i, env_ty1) => 
    List.bind (unify i (env_ty1 ++ env_ty) ty2 ty) (fun (i, env_ty2) =>
      [ (i, env_ty2 ++ env_ty1) ]
    ))
    -- list[{x;y}] | list[{x;z}] <: list[X]
    -- list[{x;y}] <: list[X]
    -- X := {x;y} | Y |- list[{x;z}] <: list[X]
    -- list[{x;z}] <: list[{x;y} | Y]

  | ty, .union ty1 ty2 => 
    (unify i env_ty ty ty1) ++ (unify i env_ty ty ty2)


  | ty, .inter ty1 ty2 => 
    List.bind (unify i env_ty ty ty1) (fun (i, env_ty1) => 
    List.bind (unify i (env_ty1 ++ env_ty) ty ty2) (fun (i, env_ty2) =>
      [ (i, env_ty2 ++ env_ty1) ]
    ))

  | .inter ty1 ty2, ty => 
    (unify i env_ty ty1 ty) ++ (unify i env_ty ty2 ty)

  | _, _ => .nil 

def unify_all (i : Nat) (cs : List (Ty × Ty)) : List (Nat × List (Nat × Ty)) := 
  List.foldl (fun u_env_ty1 => fun (ty_c1, ty_c2) => 
    List.bind u_env_ty1 (fun (i, env_ty1) => 
    List.bind (unify i env_ty1 ty_c1 ty_c2) (fun (i, env_ty2) =>
      [ (i, env_ty2 ++ env_ty1) ]
    ))
  ) [(i, [])] cs


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

def even := [: 
  μ 1 . 
    #zero ♢ |
    #succ #succ £0
:]

#eval unify 3 [] even nat_ 
#eval unify 3 [] nat_ even

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

#eval unify 3 [] 
  [: (.l #zero ♢ & .r #nil ♢) :] 
  nat_list

#eval unify 3 [] 
  [: (.l #zero ♢ & .r #dumb ♢) :] 
  nat_list

-- -- this is divergent
-- -- /-
-- -- #eval unify 3 [] 
-- --   [: (.l @0 & .r @1) :] 
-- --   nat_list
-- -- -/

#eval unify 3 [] 
  [: (.l #zero ♢ & .r @0) :] 
  nat_list

-- #eval unify 3 [] 
--   [: (.l #succ #zero ♢ & .r @0 & .g #scooby ♢) :] 
--   [: (.l #succ #zero ♢ & .r #ooga ♢ & .g #scooby ♢) | (.l #zero ♢ & .r #booga ♢) :] 


#eval unify 3 [] 
  [: (.l #succ #zero ♢ & .r #cons @0) :] 
  nat_list

#eval unify 3 [] 
  [: (.l #succ #succ #zero ♢ & .r #cons @0) :] 
  nat_list

-- #eval unify 3 [] 
--   [: (.l #succ #zero ♢ & .r @0) :] 
--   nat_list

#eval unify 3 [] 
  [: (.l #succ #zero ♢ & .r #cons #cons @0) :] 
  nat_list


-- #eval unify 3 [] 
--   [: (.l #succ #zero ♢ & .r #cons @0) :] 
--   [: 
--       ∃ 2 :: .l £0 & .r £1 ≤ (μ 1 .
--         .l #zero ♢ & .r #nil ♢ |
--         ∃ 2 :: .l £0 & .r £1 ≤ £2 .
--           .l #succ £0 & .r #cons £1
--       ) .
--         .l #succ £0 & .r #cons £1
--   :]

-- #eval unify_all 3 [
--   ([: (.l #succ #zero ♢ & .r #cons @0) :], [: .l #succ @33 & .r #cons @44 :])
-- ]

-- #eval unify_all 3 [
--   ([: (.l #succ #zero ♢ & .r #cons @0) :], [: .l #succ @33 & .r #cons @44 :]),
--   (
--     [: .l @33 & .r @44  :], 
--     [:μ 1 .
--         .l #zero ♢ & .r #nil ♢ |
--         ∃ 2 :: .l £0 & .r £1 ≤ £2 .
--           .l #succ £0 & .r #cons £1
--     :]
--   )
-- ]

/-
  μ plus .
    ∃ N .  
      #zero ♢ × N × N | 

    ∃ X Y Z :: X, Y, Z ≤ plus .  
      #succ X × Y × #succ Z
-/
def plus := [: 
  μ 1 . 
    (∃ 1 . 
      (.x #zero ♢ & .y £0 & .z £0)) |

    (∃ 3 :: (.x £0 & .y £1 & .z £2) ≤ £3 .   
      (.x #succ £0 & .y £1 & .z #succ £2))
:]

-- #print plus

-- #eval [: (.x #zero ♢ & .y #zero ♢ & .z #zero ♢) :]  
-- #eval [: #succ #succ #zero ♢ :]  


#eval unify 3 [] [:
    .x #zero ♢ &
    .y @0 &
    .z #zero ♢
:] plus


#eval unify 3 [] [:
  (
    .x (#succ #zero ♢) &
    .y (#succ #zero ♢) &
    .z (@0)
  )
:] plus

#eval unify 3 [] [:
  (
    .x (#succ #succ #zero ♢) &
    .y (#succ #zero ♢) &
    .z (@0)
  )
:] plus

#eval unify 3 [] [:
  (
    .x (#succ #zero ♢) &
    .y (@0) &
    .z (#succ #succ #zero ♢)
  )
:] plus

-- #eval unify 3 [] [:
--   (
--     .x (#succ #zero ♢) &
--     .y (#succ #succ #zero ♢) &
--     .z (@0)
--   )
-- :] plus

#eval unify 3 [] [:
  (
    .x #succ #zero ♢ &
    .y @0 &
    .z #succ #succ #zero ♢
  )
:] plus

-- #eval unify 3 [] [:
--   (
--     .x (#succ #zero ♢) &
--     .y (@0) &
--     .z (#succ (#succ #succ (#zero ♢)))
--   )
-- :] plus

#eval unify 3 [] [:
  (
    .x (@0) &
    .y (@1) &
    .z (#succ #zero ♢)
  )
:] plus

-- #eval unify 3 [] [:
--   (
--     .x (#succ #zero ♢) &
--     .y (@0) &
--     .z (@1)
--   )
-- :] plus

-- #eval unify 3 [] [:
--   (
--     .x (@0) & -- zero & succ zero
--     .y (#succ #zero ♢) &
--     .z (@1) -- succ zero & zero
--   )
-- :] plus


-- /-
-- t ::=                             term
--   _                               hole 
--   x                               variable
--   ()                              unit
--   #l t                            tag
--   fs                              record
--   cs                              function
--   t.l                             projection
--   t t                             application
--   let x : τ = t in t              binding
--   fix t                           recursion

-- cs ::=                            cases
--   for p => t                      singleton 
--   cs ; for p => t                 extension 

-- fs ::=                            fields 
--   .l t                            singleton 
--   fs ; .l t                       extension
-- -/

-- /-

-- m ::=                             substitution map
--   ⬝                                empty
--   α / τ :: m                      extension

-- env_tm ::=                             typing environment 
--   ⬝                                empty
--   x : τ :: env_tm                      extension

-- -/

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


-- -- NOTE: there is no need to instantiate in infer. All that jazz happens in subtype/unify
-- -- the assymetry of subtyping makes it clear when to instantiate/raise/free a variable
-- -- and when to unroll a looping type

-- -- notation convetion:
--   -- prime tick marks for updated versions
--   -- numbers for new parts
--   -- no subscripts
--   -- no greek
--   -- general to specific, 
--     -- e.g. env_ty, (not ty_env)
--     -- e.g. ty_recur, (not mu_ty)


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


def Ty.refresh (i : Nat) : Ty -> (Nat × Ty)
  | .bvar id => (i + 1, Ty.bvar id) 
  | .fvar _ => (i + 1, Ty.fvar i)
  | .unit => (i + 1, .unit) 
  | .tag l ty => 
    let (i, ty) := Ty.refresh i ty 
    (i, Ty.tag l ty) 
  | .field l ty => 
    let (i, ty) := Ty.refresh i ty 
    (i, Ty.field l ty) 
  | .union ty1 ty2 => 
    let (i, ty1) := Ty.refresh i ty1
    let (i, ty2) := Ty.refresh i ty2
    (i, .union ty1 ty2)
  | .inter ty1 ty2 => 
    let (i, ty1) := Ty.refresh i ty1
    let (i, ty2) := Ty.refresh i ty2
    (i, .inter ty1 ty2)
  | .case ty1 ty2 => 
    let (i, ty1) := Ty.refresh i ty1
    let (i, ty2) := Ty.refresh i ty2
    (i, .case ty1 ty2)
  | .univ n (cty1, cty2) ty => 
    let (i, cty1) := Ty.refresh i cty1
    let (i, cty2) := Ty.refresh i cty2
    let (i, ty) := Ty.refresh i ty
    (i, .univ n (cty1, cty2) ty)
  | .exis n (cty1, cty2) ty => 
    let (i, cty1) := Ty.refresh i cty1
    let (i, cty2) := Ty.refresh i cty2
    let (i, ty) := Ty.refresh i ty
    (i, .exis n (cty1, cty2) ty)
  | .recur ty =>
    let (i, ty) := Ty.refresh i ty
    (i, .recur ty)
  | .corec ty =>
    let (i, ty) := Ty.refresh i ty
    (i, .corec ty)

-- partial def Ty.union_all : (List Ty) -> Option Ty
--   | [] => none
--   | t::ts =>
--     let ts := List.filter
--       (fun t' => not (Ty.equal_syntax t t'))
--       ts
--     match Ty.union_all ts with
--       | .none => .some t
--       | .some t' => Ty.union t t'


-- partial def Ty.collapse 
--   (i : Nat) (env_ty : List (Nat × Ty)) 
--   (u_env_ty_x: List (Nat × List (Nat × Ty))) (ty : Ty): 
-- List (Nat × Ty) :=
--   let list_ty := List.map 
--     (fun (_, env_ty_ext) =>
--       Ty.reduce (env_ty_ext ++ env_ty) ty
--     ) u_env_ty_x 
--   match (Ty.union_all list_ty) with
--     | .some ty => [ (Ty.refresh i ty) ]
--     | .none => []

  -- partial def Ty.intersect_all : (List (Option Ty)) -> Option Ty
  --   | [] => none
  --   | .none :: _ => none 
  --   | .some ty_fd :: ts => 
  --     bind (Ty.intersect_all ts) (fun ty_fds => Ty.inter ty_fd ty_fds)

  -- def Ty.compact_union : Ty -> Ty -> Ty
  --   | ty, (Ty.union ty1 ty2) => 
  --     if Ty.equal_syntax ty ty1 then
  --       Ty.union ty1 ty2
  --     else
  --       Ty.union ty (Ty.union ty1 ty2)
  --   | ty, uty =>
  --     if Ty.equal_syntax ty uty then
  --       uty
  --     else
  --       Ty.union ty uty 

  -- def Ty.resolve_union (i : Nat) (u_env_ty : List (T × List (Nat × Ty))) (ty : Ty) : (Nat × Ty) := 
  --   List.foldl (fun (i, uty) => fun (_, env_ty) =>
  --     let (i, ty) := Ty.refresh i (Ty.reduce env_ty ty) 
  --     (i, Ty.compact_union ty uty)
  --   ) (i + 1, .fvar i) u_env_ty 

-- /-
-- NOTE: infer returns a refined type in addition the type variable assignments
-- assignments alone do not refine enough due to subtyping
-- NOTE: deconstructing types is reduced to unification 
-- -/
partial def infer 
  (i : Nat)
  (env_ty : List (Nat × Ty)) (env_tm : List (Nat × Ty)) (t : Tm) (ty : Ty) : 
  List (Nat × (List (Nat × Ty)) × Ty) := match t with
  | Tm.hole => .nil
  | Tm.unit => 
    List.bind (unify i env_ty Ty.unit ty) (fun (i, env_ty_x) => 
      [(i, env_ty_x, Ty.unit)]
    )
  | .bvar _ => .nil 
  | .fvar id =>
    match (lookup id env_tm) with 
      | .some ty' => 
        List.bind (unify i env_ty ty' ty) (fun (i, env_ty_x) =>
          [(i, env_ty_x, ty')]
        )
      | .none => .nil 

  | .tag l t1 =>   
    let (i, ty1) := (i + 1, .fvar i)
    List.bind (unify i env_ty (Ty.tag l ty1) ty) (fun (i, env_ty1) =>
    List.bind (infer i (env_ty1 ++ env_ty) env_tm t1 ty1) (fun (i, env_ty_x, ty1') =>
      [ (i, env_ty_x ++ env_ty1, Ty.tag l ty1') ]
    ))

  | .record fds =>
    let (i, trips) := List.foldl (fun (i, ty_acc) => fun (l, t1) =>
      (i + 1, (l, t1, (Ty.fvar i)) :: ty_acc)
    ) (i, []) fds

    match trips with
    | [] => .nil
    | hd :: tl =>
      let (l, t1, ty1) := hd
      let ty' := List.foldl (fun ty_acc => fun (l, _, ty1) => 
        Ty.inter (Ty.field l ty1) ty_acc 
      ) (Ty.field l ty1) tl 
      let u_env_ty1 := unify i env_ty ty' ty 


      let f_base := (fun (l, t1, ty1) =>
        List.bind u_env_ty1 (fun (i, env_ty1) =>
        List.bind (infer i (env_ty1 ++ env_ty) env_tm t1 ty1) (fun (i, env_ty2, ty1') =>
          [(i, env_ty2 ++ env_ty1, Ty.field l ty1')]
        ))
      )

      let f_step := fun acc => (fun (l, t1, ty1) =>
        List.bind acc (fun (i, env_ty_acc, ty_acc) =>
        List.bind (infer i (env_ty_acc ++ env_ty) env_tm t1 ty1) (fun (i, env_ty_x, ty1') =>
          [(i, env_ty_x ++ env_ty_acc, Ty.inter (Ty.field l ty1') ty_acc)]
        ))
      )

      List.foldl f_step (f_base hd) tl 

  | .func fs =>
    let (i, fs_typed) := List.foldl (fun (i, ty_acc) => fun (n, p, ty_p, b) =>
      (i + 1, (n, p, ty_p, b, (Ty.fvar i)) :: ty_acc)
    ) (i, []) fs

    match fs_typed with
    | [] => .nil
    | hd :: tl =>
      let (n, p, ty_p, b, ty_b) := hd 
      let ty' := List.foldl (fun ty_acc => fun (n, p, ty_p, b, ty_b) => 
        Ty.inter (Ty.case ty_p ty_b) ty_acc 
      ) (Ty.case ty_p ty_b) tl 
      let u_env_ty1 := unify i env_ty ty' ty 

      -- TODO: figure out how to extract variables and types from pattern
      let f_base := (fun (n, p, ty_p, b, ty_b) =>
        List.bind u_env_ty1 (fun (i, env_ty1) =>
        match (patvars env_tm p ty_p) with
        | .some env_tm1 =>
          if env_tm1.length = n then
            let (i, args) := (i + n, (List.range n).map (fun j => Tm.fvar (i + j)))
            let b := Tm.raise_binding 0 args b  
            List.bind (infer i (env_ty1 ++ env_ty) (env_tm1 ++ env_tm) b ty_b) (fun (i, env_ty2, ty_b') =>
              [(i, env_ty2 ++ env_ty1, Ty.case ty_p ty_b')]
            )
          else .nil
        | .none => .nil
        )
      )

      let f_step := fun acc => fun (n, p, ty_p, b, ty_b) =>
        List.bind acc (fun (i, env_ty_acc, ty_acc) =>
        match (patvars env_tm p ty_p) with
        | .some env_tm1 =>
          if env_tm1.length = n then
            let (i, args) := (i + n, (List.range n).map (fun j => Tm.fvar (i + j)))
            let b := Tm.raise_binding 0 args b  
            List.bind (infer i 
              (env_ty_acc ++ env_ty) (env_tm1 ++ env_tm) 
              b ty_b
            ) (fun (i, env_ty2, ty_b') =>
              [(i, env_ty2 ++ env_ty_acc, Ty.inter (Ty.case ty_p ty_b') ty_acc)]
            )
          else .nil
        | .none => .nil
        )

      List.foldl f_step (f_base hd) tl 

  | .proj t1 l =>
    List.bind (infer i env_ty env_tm t1 (Ty.field l ty)) (fun (i, env_ty1, ty1') =>
    let (i, ty') := (i + 1, Ty.fvar i)
    List.bind (unify i (env_ty1 ++ env_ty) ty1' (Ty.field l ty')) (fun (i, env_ty2) =>
      [(i, env_ty2 ++ env_ty1, ty')]
    ))

  | .app t1 t2 =>
    let (i, ty2) := (i + 1, Ty.fvar i)
    List.bind (infer i env_ty env_tm t1 (Ty.case ty2 ty)) (fun (i, env_ty1, ty1') =>
    List.bind (infer i (env_ty1 ++ env_ty) env_tm t2 ty2) (fun (i, env_ty2, ty2') =>
    let (i, ty') := (i + 1, Ty.fvar i)
    List.bind (unify i (env_ty2 ++ env_ty1 ++ env_ty) ty1' (Ty.case ty2' ty')) (fun (i, env_ty3) =>
      [(i, env_ty3 ++ env_ty2 ++ env_ty1, ty')]
    )))


  | .letb ty1 t1 t => 
    List.bind (infer i (env_ty) env_tm t1 ty1) (fun (i, env_ty1, ty1') =>
    let (i, x, env_tmx) := (i + 1, Tm.fvar i, [(i, Ty.univ 1 (Ty.bvar 0, ty1') (Ty.bvar 0))]) 
    let t := Tm.raise_binding 0 [x] t 
    List.bind (infer i (env_ty1 ++ env_ty) (env_tmx ++ env_tm) t ty) (fun (i, env_ty2, ty') =>
      [ (i, env_ty2 ++ env_ty1, ty') ]
    ))

  | .fix t1 =>
    List.bind (infer i env_ty env_tm t1 (Ty.case ty ty)) (fun (i, env_ty1, ty1') =>
    let (i, ty') := (i + 1, Ty.fvar i)
    List.bind (unify i (env_ty1 ++ env_ty) ty1' (.case ty' ty')) (fun (i, env_ty2) =>
      [ (i, env_ty2 ++ env_ty1, ty') ]
    ))
