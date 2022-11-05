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
  | corec : Ty -> Ty


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
syntax:60 slm:60 "|" slm:61 : slm
syntax:60 slm:60 "+" slm:61 : slm
syntax:70 slm:70 "&" slm:71 : slm
syntax:70 slm:70 "×" slm:71 : slm
syntax "∀" slm "::" slm "≤" slm "." slm : slm 
syntax "∀" slm "." slm : slm 
syntax "∃" slm "::" slm "≤" slm  "." slm : slm 
syntax "∃" slm "." slm : slm 
syntax "μ 0 ." slm : slm 
syntax "ν 0 ." slm : slm 

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
  | `([: $a | $b :]) => `(Ty.union [: $a :] [: $b :])
  | `([: $a + $b :]) => `(Ty.union [: #inl $a :] [: #inr $b :])
  | `([: $a & $b :]) => `(Ty.inter [: $a :] [: $b :])
  | `([: $a × $b :]) => `(Ty.inter [: .left $a :] [: .right $b :])
  | `([: ∀ $a :: $b ≤ $c . $d :]) => `(Ty.univ [: $a :] ([: $b :], [: $c :]) [: $d :])
  | `([: ∀ $a:slm . $b:slm :]) => `(Ty.univ [: $a :] ([: £$a :], [: ? :]) [: $b :] )
  | `([: ∃ $a :: $b ≤ $c . $d  :]) => `(Ty.exis [: $a :] ([: $b :], [: $c :]) [: $d :])
  | `([: ∃ $a:slm . $b:slm :]) => `(Ty.exis [: $a :] ([: £$a :], [: ? :]) [: $b :] )
  | `([: μ 0 . $a :]) => `(Ty.recur [: $a :])
  | `([: ν 0 . $a :]) => `(Ty.corec [: $a :])

-- generic
  | `([: ($a) :]) => `([: $a :])

--escape 
  | `([: ⟨ $e ⟩ :]) => pure e

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
#check [: μ 0 . #foo £0 :]
#check [: μ 0 . #foo £0  & ? | @2 & ?:]
#check [: £3 & ? -> @1 | @2 :]
#check [: μ 0 . #foo £0 & ? | @2 & ? -> @1 | @2 :]
#check [: μ 0 . #foo £0 & ? | @2 & ? :]
#check [: ? :]

def lookup (key : Nat) : List (Nat × T) -> Option T
  | (k,v) :: bs => if key = k then some v else lookup key bs 
  | [] => none

def liberate (i : Nat) : Nat -> List (Nat × Ty) 
  | 0 => []
  | n + 1 => (i, [: ? :]) :: (liberate (i + 1) n)

def refresh (i : Nat) (n : Nat) : (Nat × List (Nat × Ty) × List Ty) := 
  let args := (List.range n).map (fun j => .fvar (i + j))
  let env_ty' :=  liberate i n 
  let i' := i + n 
  (i', env_ty', args)


partial def merge (op : T -> T -> T) (df : T) (env_ty1 : List (Nat × T))  (env_ty2 : List (Nat × T)) : List (Nat × T) :=
  List.bind env_ty1 (fun (key₁, v₁) =>
  List.bind env_ty2 (fun (key₂, v₂) =>
    let uno := match lookup key₁ env_ty2 with
      | some v₂ => [(key₁, op v₁ v₂)]
      | none => [(key₁, op v₁ df)] 

    let dos := match lookup key₂ env_ty1 with
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
  | .variant l ty => (Ty.occurs key ty) 
  | .field l ty => (Ty.occurs key ty)
  | [: ⟨ty1⟩ | ⟨ty2⟩ :] => (Ty.occurs key ty1) ∨ (Ty.occurs key ty2)
  -- | .union ty1 ty2 => (Ty.occurs key ty1) ∨ (Ty.occurs key ty2)
  | .inter ty1 ty2 => (Ty.occurs key ty1) ∨ (Ty.occurs key ty2)
  | .func ty1 ty2 => (Ty.occurs key ty1) ∨ (Ty.occurs key ty2)
  | .univ n (ty_c1, ty_c2) ty => (Ty.occurs key ty_c1) ∨ (Ty.occurs key ty_c2) ∨ (Ty.occurs key ty)
  | .exis n (ty_c1, ty_c2) ty => (Ty.occurs key ty_c1) ∨ (Ty.occurs key ty_c2) ∨ (Ty.occurs key ty)
  | .recur ty => (Ty.occurs key ty)
  | .corec ty => (Ty.occurs key ty)

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
  | .union ty1 ty2 => .union (Ty.free_subst m ty1) (Ty.free_subst m ty2)
  | .inter ty1 ty2 => .inter (Ty.free_subst m ty1) (Ty.free_subst m ty2)
  | .func ty1 ty2 => .func (Ty.free_subst m ty1) (Ty.free_subst m ty2)
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
  | .union ty1 ty2 => .union (Ty.raise_binding start args ty1) (Ty.raise_binding start args ty2)
  | .inter ty1 ty2 => .inter (Ty.raise_binding start args ty1) (Ty.raise_binding start args ty2)
  | .func ty1 ty2 => .func (Ty.raise_binding start args ty1) (Ty.raise_binding start args ty2)
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
#check [: ⟨τ⟩ ↑ 0 / [μ 0 . ⟨τ⟩]:]



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
  | .union ty1 ty2 => .union (Ty.lower_binding depth ty1) (Ty.lower_binding depth ty2)
  | .inter ty1 ty2 => .inter (Ty.lower_binding depth ty1) (Ty.lower_binding depth ty2)
  | .func ty1 ty2 => .func (Ty.lower_binding depth ty1) (Ty.lower_binding depth ty2)
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


partial def roll (key : Nat) (τ : Ty) : Ty :=
  if Ty.occurs key τ then
    [: (μ 0 . ⟨τ⟩↓1) % [⟨key⟩ / £0] :]
  else
    τ



def make_record_constraint_recur (prev_ty : Ty) : Ty -> Ty -> List (Ty × Ty) 
  | (.field l ty'), mu_ty => 
      let ty := .exis 1 ( 
        (Ty.inter (Ty.lower_binding 1 prev_ty) (.field l (.bvar 0))),
        (Ty.lower_binding 1 (unroll mu_ty))
      ) (.bvar 0)
      [(ty', ty)]
  | .inter (.field l ty') rem_ty, mu_ty => 
      let ty := 
      [: ∃ 1 :: (⟨prev_ty⟩↓1 & (#⟨l⟩ £0) & ⟨rem_ty⟩↓1) ≤ ⟨unroll mu_ty⟩↓1 . £0 :]

      let rem := make_record_constraint_recur (Ty.inter prev_ty (.field l ty')) rem_ty mu_ty
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

      let rem := make_record_constraint_recur (Ty.inter prev_ty (.field l ty')) rem_ty mu_ty
      if rem.length = 0 then
        []
      else 
        (ty', ty) :: rem
  | _, _ => [] 

def make_record_constraint_corec (prev : Ty) : Ty -> Ty -> List (Ty × Ty) 
  | nu_ty, (.field l ty') => 
      let ty := .univ 1 ( 
        (Ty.lower_binding 1 (unroll nu_ty)),
        (Ty.inter (Ty.lower_binding 1 prev) (.field l (.bvar 0))) 
      ) (.bvar 0)
      [(ty', ty)]
  | nu_ty, .inter (.field l ty') rem_ty => 
      let ty := .univ 1 (
        (Ty.lower_binding 1 (unroll nu_ty)),
        (Ty.inter (
          Ty.inter (Ty.lower_binding 1 prev) (.field l (.bvar 0))) 
          (Ty.lower_binding 1 rem_ty)
        ) 
      ) (.bvar 0)

      let rem := make_record_constraint_corec (Ty.inter prev (.field l ty')) nu_ty rem_ty
      if rem.length = 0 then
        []
      else
        (ty', ty) :: rem
  | nu_ty, .inter rem_ty (.field l ty') => 
      -- copy and paste above case (for terminateion proved by structure)
      let ty := .univ 1 ( 
        (Ty.lower_binding 1 (unroll nu_ty)),
        (Ty.inter (
          Ty.inter (Ty.lower_binding 1 prev) (.field l (.bvar 0))) 
          (Ty.lower_binding 1 rem_ty)
        ) 
      ) (.bvar 0)

      let rem := make_record_constraint_corec (Ty.inter prev (.field l ty')) nu_ty rem_ty
      if rem.length = 0 then
        []
      else
        (ty', ty) :: rem
  | _, _ => [] 


partial def unify (i : Nat) (env_ty : List (Nat × Ty)) : Ty -> Ty -> Option (Nat × List (Nat × Ty))

  | .fvar id, ty  => match lookup id env_ty with 
    | none => some (i + 2, [(i, .inter (roll id ty) (Ty.fvar (i + 1)))]) 
    | some Ty.unknown => some (i + 2, [(i, .inter (roll id ty) (Ty.fvar (i + 1)))]) 
    | some ty' => unify i env_ty ty' ty 

  | ty', .fvar id  => match lookup id env_ty with 
    | none => some (i + 2, [(i, .union (roll id ty') (Ty.fvar (i + 1)))]) 
    | some Ty.unknown => some (i + 2, [(i, .union (roll id ty') (Ty.fvar (i + 1)))]) 
    | some ty => unify i env_ty ty' ty 

  -- | .recur ty', .recur ty =>
    -- TODO: should these be equal or unified?
    -- probably just equal;
    -- the assymetrical case will unroll
    -- this is the base case 
    -- unify i env_ty ty' ty 

  | .variant l ty', .recur ty =>
    unify i env_ty (.variant l ty') (unroll ty)

  | ty', .recur ty =>
    let cs := (make_record_constraint_recur Ty.unknown ty' ty)
    if cs.length = 0 then
      none
    else
      List.foldl (fun 
        | some (i, env_ty), (ty_c1, ty_c2) => unify i env_ty ty_c1 ty_c2
        | none, _ => none
      ) (some (i, env_ty)) cs


  -- | .corec ty', .corec ty =>
  -- TODO: check equality

  -- TODO: check function against corecursive type 
  -- | .corec ty', ty =>
  --   let cs := (make_record_constraint_super Ty.unknown ty' ty) 
  --   if cs.length = 0 then
  --     none
  --   else
  --     List.foldl (fun 
  --       | some (i, env_ty), (ty_c1, ty_c2) => unify i env_ty ty_c1 ty_c2
  --       | none, _ => none
  --     ) (some (i, env_ty)) cs

  | .union ty1 ty2, ty => 
    bind (unify i env_ty ty1 ty) (fun (i, env_ty1) => 
    bind (unify i env_ty ty2 ty) (fun (i, env_ty2) =>
      some (i, merge Ty.inter Ty.unknown env_ty1 env_ty2)
    ))
    -- list[{x;y}] | list[{x;z}] <: ∃ X . list[X]
    -- list[{x;y}] <: ∃ X . list[X]
    -- list[{x;z}] <: ∃ X . list[X]
    -- X <: {x;y} & {x;z} 

  | ty, .union ty1 ty2 => 
    bind (unify i env_ty ty ty1) (fun (i, env_ty1) => 
    bind (unify i env_ty ty ty2) (fun (i, env_ty2) =>
      some (i, merge Ty.union Ty.unknown env_ty1 env_ty2)
    ))

  | ty, .inter ty1 ty2 => 
    bind (unify i env_ty ty ty1) (fun (i, env_ty1) => 
    bind (unify i env_ty ty ty2) (fun (i, env_ty2) =>
      some (i, merge Ty.inter Ty.unknown env_ty1 env_ty2)
    ))

  | .inter ty1 ty2, ty => 
    bind (unify i env_ty ty1 ty) (fun (i, env_ty1) => 
    bind (unify i env_ty ty2 ty) (fun (i, env_ty2) =>
      some (i, merge Ty.union Ty.unknown env_ty1 env_ty2)
    ))

  | .func ty1 ty2', .func ty1' ty2 =>
    bind (unify i env_ty ty1' ty1) (fun (i, env_ty1) => 
    bind (unify i env_ty ty2' ty2) (fun (i, env_ty2) =>
      some (i, merge Ty.inter Ty.unknown env_ty1 env_ty2)
    ))

  | .variant l' ty', .variant l ty =>
    if l' = l then
      unify i env_ty ty' ty
    else
      none

  | .field l' ty', .field l ty =>
    if l' = l then
      unify i env_ty ty' ty
    else
      none

  -- | .exis n' (ty_c1', ty_c2') τ', .exis n (ty_c1, ty_c2) τ =>
  -- TODO: check equality

  | ty', .exis n (ty_c1, ty_c2) ty =>
    let (i, env_ty, args) := refresh i n 
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


  -- | .univ n' (ty_c1', ty_c2') τ', .univ n (ty_c1, ty_c2) τ =>
  -- TODO: check equality

  | .univ n (ty_c1, ty_c2) ty', ty =>
    let (i, env_ty, args) := refresh i n 
    let ty_c1 := Ty.raise_binding 0 args ty_c1
    let ty_c2 := Ty.raise_binding 0 args ty_c2
    let ty' := Ty.raise_binding 0 args ty'
    bind (unify i env_ty ty_c1 ty_c2) (fun (i, env_ty1) => 
    bind (unify i (env_ty1 ++ env_ty) ty' ty) (fun (i, env_ty2) =>
      some (i, env_ty2 ++ env_ty1)
    ))

  | .bvar id1, .bvar id2  =>
    if id1 = id2 then 
      some (i, [])
    else
      none

  | .unit, .unit => some (i, []) 
  | .unknown, _ => some (i, []) 
  | _, .unknown => some (i, []) 
  | _, _ => none


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

env_tm ::=                             typing environment 
  ⬝                                empty
  x : τ :: env_tm                      extension

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

`patvars t = o[env_tm]`
```
patvars x τ = 
  some {x : τ}
patvars (.l t₁) τ = 
  map (project τ l) (τ1 =>
    patvars t₁ τ1
  )
patvars (.l t fs) τ =
  map (patvars (.l t) τ) (env_tm₁ =>
  map (patvars fs τ) (env_tm₂ =>
    some (env_tm₁ ++ env_tm₂)
  ))
...
```
-/

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

def fresh (i : Nat) : Nat × Ty :=
  (i + 1, .fvar i)

partial def infer 
  (i : Nat)
  (env_ty : List (Nat × Ty)) (env_tm : List (Nat × Ty)) (t : Tm) (ty : Ty) : 
  Option (Nat × List (Nat × Ty) × Ty) := match t with
  | .unit => bind (unify i env_ty Ty.unit ty) (fun (i, env_ty) =>
      (i, env_ty, Ty.unit)
    )
  | .bvar _ => none
  | .fvar x =>
    bind (lookup x env_tm) (fun ty' =>
    bind (unify i env_ty ty' ty) (fun (i, env_ty1) =>
      some (i, env_ty1 ++ env_ty, ty')
    )) 

  | .variant l t1 =>   
    let (i, ty1) := (fresh i) 
    bind (unify i env_ty (.variant l ty1) ty) (fun (i, env_ty1) =>
    bind (infer i (env_ty1 ++ env_ty) env_tm t1 ty1) (fun (i, env_ty2, ty1') =>
      some (i, env_ty2 ++ env_ty1, .variant l ty1')
    ))

  | Tm.record [] => none

  | Tm.record ((l, t1) :: .nil) =>
    let (i, ty1) := (fresh i) 
    bind (unify i env_ty (.field l ty1) ty) (fun (i, env_ty1) =>
    bind (infer i (env_ty1 ++ env_ty) env_tm t1 ty1) (fun (i, env_ty2, ty1') =>
      some (i, env_ty2 ++ env_ty1, .field l ty1')
    ))

  | Tm.record (fd :: fds) =>
    bind (infer i env_ty env_tm (.record fds) ty) (fun (i, env_ty_fds, ty_fds) =>
    bind (infer i env_ty env_tm (.record [fd]) ty) (fun (i, env_ty_fd, ty_fd) =>
      some (i, env_ty_fd ++ env_ty_fds, .inter ty_fd ty_fds)
    ))
  | _ => none

/-
```

infer env_tm env_ty ⊢ (for t₁ : τ1 => t₂) : τ =
  let env_ty1, τ1 = τ1[?/fresh] in
  let env_tm₁ = patvars t₁ τ1 in
  let β = fresh in
  bind (solve env_ty ⊢ (∀ env_ty1 ++ {β} . τ1 -> β) ⊆ τ) (env_ty' => 
  bind (infer (env_tm ++ env_tm₁) (env_ty ++ env_ty') ⊢ t₂ : β) (env_ty2', τ2' =>
    -- patvars (env_tm₁) are NOT generalized in τ2'
    some (env_ty' ++ env_ty2' , τ1 -> τ2')
  ))


infer env_tm env_ty ⊢ (for t₁ : τ1 => t₂) cs : τ =
  bind (infer env_tm env_ty ⊢ (for t₁ : τ1 => t₂) : τ) (env_ty', τ' =>
  bind (infer env_tm env_ty ++ env_ty' ⊢ cs : τ2) (env_ty'', τ'' => 
    some (env_ty' ++ env_ty'' , τ' & τ'')
  ))

infer env_tm env_ty ⊢ t t₁ : τ2 =
  bind (infer env_tm env_ty ⊢ t : ? -> τ2 in) (env_ty',τ' => 
  bind (functify τ') (τ1,τ2' => 
  -- break type (possibly intersection) into premise and conclusion 
  bind (infer env_tm (env_ty ++ env_ty') ⊢ t₁ : τ1) (env_ty1',τ1' =>
  bind (solve env_ty ++ env_ty' ++ env_ty1' ⊢ τ' ⊆ (τ1' -> τ2)) (env_ty' =>
    some(env_ty' , τ2' & τ2)
  ))))


infer env_tm env_ty ⊢ t.l : τ2 =
  bind (infer env_tm env_ty ⊢ t : (.l τ2)) (env_ty' , τ' =>
  bind (project τ' l) (τ2' => 
    some(env_ty' , τ2')
  ))

infer env_tm env_ty ⊢ fix t : τ =
  bind (infer env_tm env_ty ⊢ t : (τ -> τ)) (env_ty',τ' =>
  bind (functify τ') (τ1', τ2' =>
    -- extract premise and conclusion 
    some(env_ty' , τ2')
  ))

infer env_tm env_ty ⊢ (let x : τ1 = t₁ in t₂) : τ2 =
  let env_ty1,τ1 = τ1[?/fresh] in
  bind (infer env_tm env_ty ⊢ t₁ : (∀ env_ty1 . τ1)) (env_ty1' , τ1' => 
  bind (infer (env_tm ++ {x : (∀ env_ty1' . τ1')}) env_ty ⊢ t₂ : τ2) (env_ty2' , τ2' =>
    -- τ1' is generalized in τ2'
    some(env_ty2' , τ2')
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
  - i.e. (τ1 \ τ2) ⊆ (τ1 & ¬ τ2), where ⊤ / τ2 = ¬ τ2)
-/
