import Init.Data.Hashable
import Lean.Data.AssocList
import Lean.Data.PersistentHashMap
open Lean PersistentHashMap
open Std

inductive Ty : Type
  | bvar : Nat -> Ty  
  | fvar : Nat -> Ty
  | unit : Ty
  | tag : String -> Ty -> Ty
  | field : String -> Ty -> Ty
  | union : Ty -> Ty -> Ty
  | inter : Ty -> Ty -> Ty
  | case : Ty -> Ty -> Ty
  | univ : Nat -> Ty -> Ty -> Ty -> Ty
  | exis : Nat -> Ty -> Ty -> Ty -> Ty
  | recur : Ty -> Ty
  | corec : Ty -> Ty
  deriving Repr, Inhabited, Hashable, BEq


protected def Ty.repr (ty : Ty) (n : Nat) : Format :=
match ty, n with
| .bvar id, _ => 
  "Z." ++ repr id
| .fvar id, _ =>
  "X." ++ repr id
| .unit, _ => "@" 
| .tag l ty1, _ => 
  (l ++ "^" ++ (Ty.repr ty1 n))
| .field l ty1, _ => 
  (l ++ "~" ++ (Ty.repr ty1 n))
| .union ty1 ty2, _ =>
  Format.bracket "(" ((Ty.repr ty1 n) ++ " |" ++ Format.line ++ (Ty.repr ty2 n)) ")"
| .inter ty1 ty2, _ =>
  Format.bracket "(" ((Ty.repr ty1 n) ++ " ;" ++ Format.line ++ (Ty.repr ty2 n)) ")"
| .case ty1 ty2, _ =>
  Format.bracket "(" ((Ty.repr ty1 n) ++ " ->" ++ Format.line ++ (Ty.repr ty2 n)) ")"
| .univ n ty_c1 ty_c2 ty_pl, _ =>
  "∀ " ++ (repr n) ++ " :: " ++
  (Ty.repr ty_c1 n) ++ " ≤ " ++ (Ty.repr ty_c2 n) ++ " ." ++ Format.line ++ 
  (Ty.repr ty_pl n)
| .exis n ty_c1 ty_c2 ty_pl, _ =>
  "∃ " ++ (repr n) ++ " :: " ++
  (Ty.repr ty_c1 n) ++ " ≤ " ++ (Ty.repr ty_c2 n) ++ " ." ++ Format.line ++ 
  (Ty.repr ty_pl n)
| .recur ty1, _ =>
  "μ Z.0 . " ++ (Ty.repr ty1 n)
| .corec ty1, _ =>
  "ν Z.0 . " ++ (Ty.repr ty1 n)

instance : Repr Ty where
  reprPrec := Ty.repr


inductive Tm : Type
  | hole : Tm 
  | unit : Tm
  | bvar : Nat -> Tm 
  | fvar : Nat -> Tm 
  | tag : String -> Tm -> Tm
  | record : List (String × Tm) -> Tm
  | func : List (Tm × Option Ty × Tm) -> Tm
  | proj : Tm -> String -> Tm
  | app : Tm -> Tm -> Tm
  | letb : Option Ty -> Tm -> Tm -> Tm
  | fix : Tm -> Tm
  deriving Repr, Inhabited, BEq

def indent(n : Nat) : String :=
  Nat.fold (fun | _, acc => acc ++ "  " ) n ""

protected partial def Tm.repr (t : Tm) (n : Nat) : Format :=
match t with
| .hole => 
  "_"
| .unit =>
  "()"
| .bvar id =>
  "z." ++ repr id
| .fvar id => 
  "x." ++ repr id
| .tag l t1 =>
  l ++ "/" ++ (Tm.repr t1 n)
| record fds =>
  let _ : ToFormat (String × Tm) := ⟨fun (l, t1) =>
    l ++ " := " ++ Tm.repr t1 n ⟩
  "R " ++ Format.bracket "[" (Format.joinSep fds ("," ++ Format.line)) "]"
| func fs =>
  let _ : ToFormat (Tm × Option Ty × Tm) := ⟨fun (pat, op_ty_pat, tb) =>
    match op_ty_pat with
    | .some ty_pat =>
      (Tm.repr pat n) ++ " : " ++ (Ty.repr ty_pat n) ++ 
      " => " ++ (Tm.repr tb (n))
    | .none =>
      (Tm.repr pat n) ++ " => " ++ (Tm.repr tb (n))
  ⟩
  "F " ++ Format.bracket "[" (Format.joinSep fs (",\n")) "]"
| .proj t1 l =>
  Tm.repr t1 n ++ "." ++ l
| .app t1 t2 =>
  Format.bracket "(" (Tm.repr t1 n) ")" ++ Tm.repr t2 n
| .letb op_ty1 t1 t2 =>
  match op_ty1 with
  | .some ty1 =>
    "let z.0 : " ++ (Ty.repr ty1 n) ++ " = " ++  (Tm.repr t1 n) ++ " ." ++
    Format.line  ++ (Tm.repr t2 n) 
  | .none =>
    "let z.0 " ++ " = " ++  (Tm.repr t1 n) ++ " ." ++
    Format.line  ++ (Tm.repr t2 n) 
| .fix t1 =>
  Format.bracket "(" ("fix " ++ (Tm.repr t1 n)) ")"


instance : Repr Tm where
  reprPrec := Tm.repr


declare_syntax_cat slm
syntax num : slm 
syntax ident : slm
syntax "[" slm,+ "]" : slm 
-- type
syntax "Z."slm:90 : slm
syntax "X."slm:90 : slm
syntax "@" : slm
syntax slm:90 "^" slm:90 : slm
syntax slm:90 "~" slm:90 : slm
syntax:50 slm:50 "->" slm:51 : slm
syntax:60 slm:60 "|" slm:61 : slm
syntax:60 slm:60 "+" slm:61 : slm
syntax:64 "∃" slm "::" slm "≤" slm  "." slm:65 : slm 
syntax:64 "∃" slm "." slm:65 : slm 
syntax:70 slm:70 ";" slm:71 : slm
syntax:70 slm:70 "×" slm:71 : slm
syntax:74 "∀" slm "::" slm "≤" slm "." slm:75 : slm 
syntax:74 "∀" slm "." slm:75 : slm 
syntax "μ Z.0 ." slm : slm 
syntax "ν Z.0 ." slm : slm 

--term
syntax:100 "_" : slm
syntax:100 "()" : slm
syntax:100 "z." slm:100 : slm
syntax:100 "x." slm:100 : slm
syntax:100 slm:100 "/" slm:100 : slm
syntax:100 slm:100 ":=" slm:100 : slm
syntax:100 "R" slm : slm
syntax:99 "for" slm:100 ":" slm "=>" slm:99 : slm 
syntax:99 "for" slm:100 "=>" slm:99 : slm 
syntax:100 "F" slm : slm 
syntax:100 "(" slm:100 "." slm:100 ")" : slm 
syntax:100 "(" slm:100 slm:100 ")" : slm 
syntax:100 "let z.0" ":" slm:100 "=" slm:100 "." slm:100 : slm 
syntax:100 "let z.0" "=" slm:100 "." slm:100 : slm 
syntax:100 "fix " slm:100 : slm 

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
  | `([: Z.$n :]) => `(Ty.bvar [: $n :])
  | `([: X.$n:slm :]) => `(Ty.fvar [: $n :])
  | `([: @ :]) => `(Ty.unit)
  | `([: $a ^ $b:slm :]) => `(Ty.tag [: $a :] [: $b :])
  | `([: $a ~ $b:slm :]) => `(Ty.field [: $a :] [: $b :])
  | `([: $a -> $b :]) => `(Ty.case [: $a :] [: $b :])
  | `([: $a | $b :]) => `(Ty.union [: $a :] [: $b :])
  | `([: $a + $b :]) => `(Ty.union [: inl ^ $a :] [: inr ^ $b :])
  | `([: $a ; $b :]) => `(Ty.inter [: $a :] [: $b :])
  | `([: $a × $b :]) => `(Ty.inter [: left ~ $a :] [: right ~ $b :])
  | `([: ∀ $a :: $b ≤ $c . $d :]) => `(Ty.univ [: $a :] [: $b :] [: $c :] [: $d :])
  | `([: ∀ $a:slm . $b:slm :]) => `(Ty.univ [: $a :] [: Z.$a :] [: Z.$a :] [: $b :] )
  | `([: ∃ $a :: $b ≤ $c . $d  :]) => `(Ty.exis [: $a :] [: $b :] [: $c :] [: $d :])
  | `([: ∃ $a:slm . $b:slm :]) => `(Ty.exis [: $a :] [: Z.$a :] [: Z.$a :] [: $b :] )
  | `([: μ Z.0 . $a :]) => `(Ty.recur [: $a :])
  | `([: ν Z.0 . $a :]) => `(Ty.corec [: $a :])
--Tm
  | `([: _ :]) => `(Tm.hole)
  | `([: () :]) => `(Tm.unit)
  | `([: x.$n :]) => `(Tm.bvar [: $n :])
  | `([: z.$n :]) => `(Tm.fvar [: $n :])
  | `([: $a / $b :]) => `(Tm.tag [: $a :] [: $b :])
  | `([: $a := $b :]) => `(([: $a :], [: $b :]))
  | `([: for $b : $c => $d :]) => `(([: $b :], Option.some [: $c :], [: $d :]))
  | `([: for $b => $d :]) => `(([: $b :], Option.none, [: $d :]))
  | `([: R $a :]) => `(Tm.record [: $a :])
  | `([: F $a :]) => `(Tm.func [: $a :])
  | `([: ($a . $b) :]) => `(Tm.proj [: $a :] [: $b :])
  | `([: ($a $b) :]) => `(Tm.app [: $a :] [: $b :])
  | `([: let z.0 : $a = $b . $c :]) => `(Tm.letb (Option.some [: $a :]) [: $b :] [: $c :])
  | `([: let z.0 = $b . $c :]) => `(Tm.letb Option.none [: $b :] [: $c :])
  | `([: fix $a :]) => `(Tm.fix [: $a :])

-- generic
  | `([: ($a) :]) => `([: $a :])

--escape 
  | `([: ⟨ $e ⟩ :]) => pure e

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
cases_normal (/l₁ τ1) (/l₂ τ2) = true
cases_normal τ1 τ2 = 
  fmap (keys τ1) (ks₁ =>
  fmap (keys τ2) (ks₂ =>
    some (ks₁ = ks₂)
  )) = Some true
  (keys τ1) = (keys τ2) 
```


`decreasing τ τ = b`
```
decreasing (/l τ) τ = true 
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
  | .univ n ty_c1 ty_c2 ty => (Ty.occurs key ty_c1) ∨ (Ty.occurs key ty_c2) ∨ (Ty.occurs key ty)
  | .exis n ty_c1 ty_c2 ty => (Ty.occurs key ty_c1) ∨ (Ty.occurs key ty_c2) ∨ (Ty.occurs key ty)
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
  | .univ n ty_c1 ty_c2 ty => (.univ n 
    (Ty.free_subst m ty_c1) (Ty.free_subst m ty_c2)
    (Ty.free_subst m ty)
  )
  | .exis n ty_c1 ty_c2 ty => (.exis n
    (Ty.free_subst m ty_c1) (Ty.free_subst m ty_c2) 
    (Ty.free_subst m ty)
  )
  | .recur ty => .recur (Ty.free_subst m ty)
  | .corec ty => .corec (Ty.free_subst m ty)


declare_syntax_cat sub
syntax slm "//" slm : sub 
syntax "[" sub,+ "]" : sub
syntax "[sub:" sub ":]" : term 

macro_rules
  | `([sub: $a:slm // $b:slm :]) => `(([: $a :], [: $b :])) 

macro_rules
  | `([sub: [$x:sub] :]) => `([ [sub: $x :] ])
  | `([sub: [$x,$xs:sub,*] :]) => `([sub: $x :] :: [sub: [$xs,*] :])


syntax slm "%" sub : slm 
macro_rules
  | `([: $a % $b:sub :]) => `(Ty.free_subst [sub: $b :] [: $a :])


-- #check [: (Z.1) % [1 // X.0] :]
#check [: (Z.1) % [1//X.0] :]

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
| .univ n ty_c1 ty_c2 ty => (.univ n
  (Ty.raise_binding (start + n) args ty_c1) (Ty.raise_binding (start + n) args ty_c2)
  (Ty.raise_binding (start + n) args ty)
)
| .exis n ty_c1 ty_c2 ty => (.exis n
  (Ty.raise_binding (start + n) args ty_c1) (Ty.raise_binding (start + n) args ty_c2)
  (Ty.raise_binding (start + n) args ty)
)
| .recur ty => .recur (Ty.raise_binding (start + 1) args ty)
| .corec ty => .corec (Ty.raise_binding (start + 1) args ty)

syntax slm "↑" slm "//" slm : slm 

macro_rules
  | `([: $a ↑ $b // $c :]) => `(Ty.raise_binding [: $b :] [: $c :] [: $a :])


def τ := [: X.0 :]
#check [: ⟨τ⟩ ↑ 0 // [μ Z.0 . ⟨τ⟩]:]



/-
-- TODO: determine how to add co-recursive types (ν)  
-- TODO: pay attention to how recursive and co-recursive types are unrolled
-- ν and ∀ should be handled in similar ways. Don't unroll/raise until some application
  mandates a witness

---
recursive types

μ nat . zero^| succ^nat 

unroll

zero^| succ^(μ nat . zero^| succ^nat)

unroll on rhs of subtyping
can't unroll on lhs 

zero^| succ^zero^| succ^(μ nat . zero^| succ^nat)


---
co-recursive types

ν (nat -> list) . 
  zero^-> nil^; 
  succ^nat -> cons^(? × list)

desugar 

ν nat_to_list . 
  zero^-> nil^; 
  succ^nat -> cons^(? × list)
    ;> (nat -> list) ≤ nat_to_list .

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
    [: ⟨ty⟩ ↑ 0 // [μ Z.0 . ⟨ty⟩]:]
  | .corec ty => 
    -- Ty.raise_binding 0 [Ty.recur τ] τ 
    [: ⟨ty⟩ ↑ 0 // [ν Z.0 . ⟨ty⟩]:]
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
    [: (μ Z.0 . ⟨τ⟩) % [⟨key⟩ // Z.0] :]
  else
    τ

partial def roll_corec (key : Nat) (τ : Ty) : Ty :=
  if Ty.occurs key τ then
    [: (ν Z.0 . ⟨τ⟩) % [⟨key⟩ // Z.0] :]
  else
    τ

partial def Ty.reduce (env_ty : PHashMap Nat Ty) : Ty -> Ty
  | .bvar id => Ty.bvar id  
  | .fvar id => match env_ty.find? id with
    | some ty => Ty.reduce env_ty ty 
    | none => Ty.fvar id 
  | .unit => .unit 
  | .tag l ty => Ty.tag l (Ty.reduce env_ty ty) 
  | .field l ty => Ty.field l (Ty.reduce env_ty ty) 
  | .union ty1 ty2 => Ty.union (Ty.reduce env_ty ty1) (Ty.reduce env_ty ty2)
  | .inter ty1 ty2 => Ty.inter (Ty.reduce env_ty ty1) (Ty.reduce env_ty ty2)
  | .case ty1 ty2 => Ty.case (Ty.reduce env_ty ty1) (Ty.reduce env_ty ty2)
  | .univ n cty1 cty2 ty => 
      Ty.univ n  
        (Ty.reduce env_ty cty1) (Ty.reduce env_ty cty2)
        (Ty.reduce env_ty ty)
  | .exis n cty1 cty2 ty => 
      Ty.exis n  
        (Ty.reduce env_ty cty1) (Ty.reduce env_ty cty2)
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

  | .univ n1 tyc1 tyc2 ty1, .univ n2 tyc3 tyc4 ty2 =>
    n1 = n2 ∧
    Ty.equal_syntax tyc1 tyc3 ∧
    Ty.equal_syntax tyc2 tyc4 ∧
    Ty.equal_syntax ty1 ty2

  | .exis n1 tyc1 tyc2 ty1, .exis n2 tyc3 tyc4 ty2 =>
    n1 = n2 ∧
    Ty.equal_syntax tyc1 tyc3 ∧
    Ty.equal_syntax tyc2 tyc4 ∧
    Ty.equal_syntax ty1 ty2

  | .recur ty1, .recur ty2 =>
    Ty.equal_syntax ty1 ty2

  | .corec ty1, .corec ty2 =>
    Ty.equal_syntax ty1 ty2
  | _, _ => false

partial def Ty.equal (env_ty : PHashMap Nat Ty) (ty1 : Ty) (ty2 : Ty) : Bool :=
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


#check List.any

def wellformed_record_type (env_ty : PHashMap Nat Ty) (ty : Ty) : Bool :=
  match linearize_fields (Ty.reduce env_ty ty) with
    | .some fields => 
      List.any fields (fun (k_fd, ty_fd) =>
        match ty_fd with
          | .fvar _ => false 
          | _ => true 
      ) 
    | .none => false


/-
(X ; Y) <: μ _

X <: (∃ α :: ((α ; Y) <: unroll (μ _)). α)
Y <: (∃ β :: ((X ; β) <: unroll (μ _)). β)
-/
def make_field_constraints (prev_ty : Ty) : Ty -> Ty -> List (Ty × Ty) 
  | (.field l ty1), mu_ty => 
      let ty2 := .exis 1  
        (Ty.inter (prev_ty) (.field l (.bvar 0)))
        (unroll mu_ty)
        (.bvar 0)
      [(ty1, ty2)]
  | .inter (.field l ty1) rem_ty, mu_ty => 
      let ty2 := 
      [: ∃ 1 :: (⟨prev_ty⟩ ; (⟨l⟩^Z.0) ; ⟨rem_ty⟩) ≤ ⟨unroll mu_ty⟩ . Z.0 :]

      let rem := make_field_constraints (Ty.inter prev_ty (.field l ty1)) rem_ty mu_ty
      if rem.length = 0 then
        []
      else 
        (ty1, ty2) :: rem
  | _, _ => [] 


def PHashMap.insert_all [BEq α] [Hashable α] 
(base : PHashMap α β) (ext : PHashMap α β) : PHashMap α β :=
  ext.foldl (init := base) fun m k v => m.insert k v

-- instance [BEq α] [Hashable α] : Append (PHashMap α β) where
--   append := PHashMap.insert_all

infixl:65   " ;; " => PHashMap.insert_all

def PHashMap.from_list [BEq α] [Hashable α] 
(source : List (α × β)) : PHashMap α β :=
  source.foldl (init := {}) fun m (k, v) => m.insert k v

protected def PHashMap.repr [Repr (α × β)] [BEq α] [Hashable α] 
(m : PHashMap α β) (n : Nat) : Format :=
  List.repr (toList m) n

instance [Repr (α × β)] [BEq α] [Hashable α] : Repr (PHashMap α β) where
  reprPrec := PHashMap.repr


/-

result:
empty list is failure
non-empty list represents the solutions of unification


-/
-- partial def unify (i : Nat) (env_ty : List (Nat × Ty)) : 
partial def unify (i : Nat) (env_ty : PHashMap Nat Ty) : 
Ty -> Ty -> List (Nat × PHashMap Nat Ty)
  | .bvar id1, .bvar id2  =>
    if id1 = id2 then 
      [ (i, {}) ]
    else
      .nil

  | .unit, .unit => [ (i, {}) ] 

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
    List.bind (unify i (env_ty ;; env_ty1) ty2' ty2) (fun (i, env_ty2) =>
      [ (i, env_ty1 ;; env_ty2) ]
    ))

  | ty', .fvar id  => match env_ty.find? id with 
    | none => [ 
        (i + 1, PHashMap.from_list [
          (id, Ty.union (roll_corec id ty') (Ty.fvar i))
        ]) 
      ]
    | some ty => unify i env_ty ty' ty 

  | .fvar id, ty  => match env_ty.find? id with 
    | none => [ 
        (i + 1, PHashMap.from_list [
          (id, Ty.inter (roll_recur id ty) (Ty.fvar i))
        ]) 
      ]
    | some ty' => unify i env_ty ty' ty 


  | ty', .exis n ty_c1 ty_c2 ty =>
    let (i, args) := (i + n, (List.range n).map (fun j => .fvar (i + j)))

    let ty_c1 := Ty.raise_binding 0 args ty_c1
    let ty_c2 := Ty.raise_binding 0 args ty_c2
    let ty := Ty.raise_binding 0 args ty
    List.bind (unify i env_ty ty' ty) (fun (i, env_ty1) =>
    List.bind (unify i (env_ty ;; env_ty1) ty_c1 ty_c2) (fun (i, env_ty2) => 
      [ (i, env_ty1 ;; env_ty2) ]
    ))


  | .univ n ty_c1 ty_c2 ty', ty =>
    let (i, args) := (i + n, (List.range n).map (fun j => .fvar (i + j)))
    let ty_c1 := Ty.raise_binding 0 args ty_c1
    let ty_c2 := Ty.raise_binding 0 args ty_c2
    let ty' := Ty.raise_binding 0 args ty'
    List.bind (unify i env_ty ty' ty) (fun (i, env_ty1) =>
    List.bind (unify i (env_ty ;; env_ty1) ty_c1 ty_c2) (fun (i, env_ty2) => 
      [ (i, env_ty1 ;; env_ty2) ]
    ))

  | .exis n ty_c1 ty_c2 ty', ty =>
    if Ty.equal env_ty (.exis n ty_c1 ty_c2 ty') ty then
      [ (i, {})  ]
    else
      .nil

  | ty', .univ n ty_c1 ty_c2 ty =>
    if Ty.equal env_ty ty' (.univ n ty_c1 ty_c2 ty) then
      [ (i, {}) ]
    else
      .nil 

  | .recur ty', .recur ty =>
    if Ty.equal env_ty ty' ty then
      [ (i, {}) ]
    else
      let ty' := [: ⟨ty'⟩ ↑ 0 // [μ Z.0 . ⟨ty⟩]:]
      let ty := [: ⟨ty⟩ ↑ 0 // [μ Z.0 . ⟨ty⟩]:]
      unify i env_ty ty' ty

  | .tag l ty', .recur ty =>
    unify i env_ty (.tag l ty') (unroll (.recur ty))


  | ty', .recur ty =>
    if wellformed_record_type env_ty ty' then 
      unify i env_ty ty' (unroll (Ty.recur ty))
    else
      .nil

  | .corec ty', .corec ty =>
    if Ty.equal env_ty ty' ty then
      [ (i, {}) ]
    else
      let ty' := [: ⟨ty'⟩ ↑ 0 // [μ Z.0 . ⟨ty'⟩] :]
      let ty := [: ⟨ty⟩ ↑ 0 // [μ Z.0 . ⟨ty'⟩] :]
      unify i env_ty ty' ty


  | .corec ty_corec, Ty.case ty1 ty2 =>
    -- TODO: extend to more complex function types: 
      -- e.g. T -> T -> T -> T or (T × T) -> (T × T) -> ...   
    -- TODO: add wellformed_function_type check
    unify i env_ty (unroll (Ty.corec ty_corec)) (Ty.case ty1 ty2)


  | .union ty1 ty2, ty => 
    List.bind (unify i env_ty ty1 ty) (fun (i, env_ty1) => 
    List.bind (unify i (env_ty ;; env_ty1) ty2 ty) (fun (i, env_ty2) =>
      [ (i, env_ty1 ;; env_ty2) ]
    ))

  | ty, .union ty1 ty2 => 
    (unify i env_ty ty ty1) ++ (unify i env_ty ty ty2)


  | ty, .inter ty1 ty2 => 
    List.bind (unify i env_ty ty ty1) (fun (i, env_ty1) => 
    List.bind (unify i (env_ty ;; env_ty1) ty ty2) (fun (i, env_ty2) =>
      [ (i, env_ty1 ;; env_ty2) ]
    ))

  | .inter ty1 ty2, ty => 
    (unify i env_ty ty1 ty) ++ (unify i env_ty ty2 ty)

  | _, _ => .nil 

def unify_all (i : Nat) (cs : List (Ty × Ty)) : List (Nat × PHashMap Nat Ty) := 
  List.foldl (fun u_env_ty1 => fun (ty_c1, ty_c2) => 
    List.bind u_env_ty1 (fun (i, env_ty1) => 
    List.bind (unify i env_ty1 ty_c1 ty_c2) (fun (i, env_ty2) =>
      [ (i, env_ty1 ;; env_ty2) ]
    ))
  ) [(i, {})] cs


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
  | .univ n cty1 cty2 ty => 
    let (i, cty1) := Ty.refresh i cty1
    let (i, cty2) := Ty.refresh i cty2
    let (i, ty) := Ty.refresh i ty
    (i, .univ n cty1 cty2 ty)
  | .exis n cty1 cty2 ty => 
    let (i, cty1) := Ty.refresh i cty1
    let (i, cty2) := Ty.refresh i cty2
    let (i, ty) := Ty.refresh i ty
    (i, .exis n cty1 cty2 ty)
  | .recur ty =>
    let (i, ty) := Ty.refresh i ty
    (i, .recur ty)
  | .corec ty =>
    let (i, ty) := Ty.refresh i ty
    (i, .corec ty)

partial def Ty.union_all : (List Ty) -> Option Ty
  | [] => none
  | t::ts =>
    let ts := List.filter
      (fun t' => not (Ty.equal_syntax t t'))
      ts
    match Ty.union_all ts with
      | .none => .some t
      | .some t' => Ty.union t t'


partial def Ty.collapse 
  (i : Nat) (env_ty : PHashMap Nat Ty) 
  (u_env_ty_x: List (Nat × PHashMap Nat Ty)) (ty : Ty): 
List Ty :=
  List.map 
    (fun (_, env_ty_ext) =>
      Ty.reduce (env_ty ;; env_ty_ext) ty
    ) u_env_ty_x 



partial def unify_collapse (i : Nat) (env_ty) (ty1) (ty2) (ty_result) :=
  Ty.collapse i env_ty (
    unify i env_ty ty1 ty2
  ) ty_result


-- -- notation convetion:
--   -- prime tick marks for updated versions
--   -- numbers for new parts
--   -- no subscripts
--   -- no greek
--   -- general to specific, 
--     -- e.g. env_ty, (not ty_env)
--     -- e.g. ty_recur, (not mu_ty)

partial def pattern_wellformed (i : Nat) : Tm -> Option Nat
| .hole => some i 
| .unit => some i 
| .bvar id => if i == id then some (i + 1) else none
| .fvar _ => none
| .tag _ t1 => pattern_wellformed i t1 
| .record fds => 
  fds.foldl (fun 
    | .some i, (l, t1) => pattern_wellformed i t1 
    | .none, _ => none
  ) (some i)
| .func _ => none
| .proj _ _ => none
| .app _ _ => none
| .letb _ _ _ => none
| .fix _ => none

partial def Tm.raise_binding (start : Nat) (args : List Tm) : Tm -> Tm
| .hole => Tm.hole 
| .bvar id => 
    if h : start ≤ id ∧ (id - start) < args.length then
      let i : Fin args.length := {
        val := (id - start),
        isLt := (match h with | And.intro _ h' => h') 
      } 
      args.get i 
    else
      .bvar id
| .fvar id => Tm.fvar id 
| .unit => Tm.unit 
| .tag l t => Tm.tag l (Tm.raise_binding start args t)
| .record fds =>
  Tm.record (List.map (fun (l, t) =>
    (l, Tm.raise_binding start args t)
  ) fds)
| .func fs =>
  Tm.func (List.map (fun (tp, op_ty_p, tb) =>
    let n := match pattern_wellformed 0 tp with
    | .some n => n 
    | .none => 0 
    let tp := Tm.raise_binding (start + n) args tp 
    let tb := Tm.raise_binding (start + n) args tb
    (tp, op_ty_p, tb)
  ) fs)
| .proj t l => 
  Tm.proj (Tm.raise_binding start args t) l
| .app t1 t2 =>
  Tm.app 
    (Tm.raise_binding start args t1) 
    (Tm.raise_binding start args t2)
| .letb ty1 t1 t2 =>
  Tm.letb ty1 
    (Tm.raise_binding start args t1)
    (Tm.raise_binding (start + 1) args t2)
| .fix t =>
  Tm.fix (Tm.raise_binding start args t)


def Option.toList : Option T -> List T 
| .some x => [x]
| .none => []

partial def infer (i : Nat)
(env_ty : PHashMap Nat Ty) (env_tm : PHashMap Nat Ty) (t : Tm) (ty : Ty) : 
List (Nat × (PHashMap Nat Ty) × Ty) := 
match t with
| Tm.hole => .nil
| Tm.unit => 
  List.bind (unify i env_ty Ty.unit ty) (fun (i, env_ty_x) => 
    [(i, env_ty_x, Ty.unit)]
  )
| Tm.bvar _ => .nil 
| Tm.fvar id =>
  match (env_tm.find? id) with 
    | .some ty' => 
      List.bind (unify i env_ty ty' ty) (fun (i, env_ty_x) =>
        [(i, env_ty_x, ty')]
      )
    | .none => .nil 

| .tag l t1 =>   
  let (i, ty1) := (i + 1, .fvar i)
  List.bind (unify i env_ty (Ty.tag l ty1) ty) (fun (i, env_ty1) =>
  List.bind (infer i (env_ty ;; env_ty1) env_tm t1 ty1) (fun (i, env_ty_x, ty1') =>
    [ (i, env_ty1 ;; env_ty_x, Ty.tag l ty1') ]
  ))

| .record fds =>
  let (i, trips) := List.foldl (fun (i, ty_acc) => fun (l, t1) =>
    (i + 1, (l, t1, (Ty.fvar i)) :: ty_acc)
  ) (i, []) fds

  match trips with
  | [] => .nil
  | hd :: tl =>

    -- dummy type with dummy variable; could use ("" ~ ⊤) type instead
    let (i, init_ty') := (i + 1, Ty.field "" (Ty.fvar (i + 1)))

    let ty' := List.foldl (fun ty_acc => fun (l, _, ty1) => 
      Ty.inter (Ty.field l ty1) ty_acc 
    ) init_ty' (hd::tl) 

    let u_env_ty1 := unify i env_ty ty' ty 

    let f_step := fun acc => (fun (l, t1, ty1) =>
      List.bind acc (fun (i, env_ty_acc, ty_acc) =>
      List.bind (infer i (env_ty ;; env_ty_acc) env_tm t1 ty1) (fun (i, env_ty_x, ty1') =>
        [(i, env_ty_acc ;; env_ty_x, Ty.inter (Ty.field l ty1') ty_acc)]
      ))
    )

    -- dummy init with dummy variable; could use top type instead
    let init := u_env_ty1.map fun (i, env_ty1) => (i + 1, env_ty1, Ty.fvar (i + 1))
    List.foldl f_step init (hd::tl) 

| .func fs =>
  let (i, fs_typed) := List.foldl (fun (i, ty_acc) => fun (p, op_ty_p, b) =>
    (i + 1, (p, op_ty_p, b, (Ty.fvar i)) :: ty_acc)
  ) (i, []) fs

  -- dummy type with dummy variables; could use bot -> top type instead
  let (i, case_init) := (i + 2, Ty.case (Ty.fvar i) (Ty.fvar (i + 1)))

  let (i, ty') := List.foldl (fun (i, ty_acc) (p, op_ty_p, b, ty_b) => 
    let (i, ty_p) := match op_ty_p with
      | .some ty_p => (i, ty_p)
      | .none => (i + 1, Ty.fvar i)
    (i, Ty.inter (Ty.case ty_p ty_b) ty_acc) 
  ) (i, case_init) fs_typed 

  let u_env_ty1 := unify i env_ty ty' ty 

  let f_step := (fun acc (p, op_ty_p, b, ty_b) =>
    List.bind acc (fun (i, env_ty_acc, ty_acc) =>
    List.bind (pattern_wellformed 0 p).toList (fun n =>

    let env_pat : PHashMap Nat Ty := (List.range n).foldl (init := {}) (fun env_pat j => 
      let tm_key := (i + (2 * j))
      let ty_x := Ty.fvar (i + (2 * j) + 1)
      (env_pat.insert tm_key ty_x)
    )
    let i := i + (2 * n)

    let list_tm_x := env_pat.toList.map fun (k, _) => ((Tm.fvar k))

    let p := Tm.raise_binding 0 list_tm_x p 
    let (i, ty_p) := match op_ty_p with
      | .some ty_p => (i, ty_p)
      | .none => (i + 1, Ty.fvar i)

    let b := Tm.raise_binding 0 list_tm_x b  
    List.bind (infer i (env_ty ;; env_ty_acc) (env_tm ;; env_pat) p ty_p) (fun (i, env_ty_p, _) =>
    List.bind (infer i (env_ty ;; env_ty_acc ;; env_ty_p) (env_tm ;; env_pat) b ty_b) (fun (i, env_ty_b, ty_b') =>
      [(i, env_ty_acc ;; env_ty_p ;; env_ty_b, Ty.inter (Ty.case ty_p ty_b') ty_acc)]
    ))))
  )

  -- dummy init with dummy variable; could use top type instead
  let init := u_env_ty1.map fun (i, env_ty1) => (i + 1, env_ty1, Ty.fvar i)
  List.foldl f_step init fs_typed 

| .proj t1 l =>
  List.bind (infer i env_ty env_tm t1 (Ty.field l ty)) (fun (i, env_ty1, ty1') =>
  let (i, ty') := (i + 1, Ty.fvar i)
  List.bind (unify i (env_ty ;; env_ty1) ty1' (Ty.field l ty')) (fun (i, env_ty2) =>
    [(i, env_ty1 ;; env_ty2, ty')]
  ))

| .app t1 t2 =>
  let (i, ty2) := (i + 1, Ty.fvar i)
  List.bind (infer i env_ty env_tm t1 (Ty.case ty2 ty)) (fun (i, env_ty1, ty1') =>
  List.bind (infer i (env_ty ;; env_ty1) env_tm t2 ty2) (fun (i, env_ty2, ty2') =>
  let (i, ty') := (i + 1, Ty.fvar i)
  List.bind (unify i (env_ty ;; env_ty1 ;; env_ty2) ty1' (Ty.case ty2' ty')) (fun (i, env_ty3) =>
    [(i, env_ty1 ;; env_ty2 ;; env_ty3, ty')]
  )))


| .letb op_ty1 t1 t => 
  let (i, ty1) := match op_ty1 with
    | .some ty1 => (i, ty1) 
    | .none => (i + 1, Ty.fvar i)
  List.bind (infer i (env_ty) env_tm t1 ty1) (fun (i, env_ty1, ty1') =>
  let (i, x, env_tmx) := (i + 1, Tm.fvar i, PHashMap.from_list [(i, Ty.univ 1 (Ty.bvar 0) ty1' (Ty.bvar 0))]) 
  let t := Tm.raise_binding 0 [x] t 
  List.bind (infer i (env_ty ;; env_ty1) (env_tm ;; env_tmx) t ty) (fun (i, env_ty2, ty') =>
    [ (i, env_ty1 ;; env_ty2, ty') ]
  ))

| .fix t1 =>
  List.bind (infer i env_ty env_tm t1 (Ty.case ty ty)) (fun (i, env_ty1, ty1') =>
  let (i, ty') := (i + 1, Ty.fvar i)
  List.bind (unify i (env_ty ;; env_ty1) ty1' (.case ty' ty')) (fun (i, env_ty2) =>
    [ (i, env_ty1 ;; env_ty2, ty') ]
  ))


partial def infer_collapse (t : Tm) : List Ty :=
  List.bind (infer 1 {} {} t [: X.0 :]) (fun (_, env_ty, ty) =>
    [Ty.reduce env_ty ty]
  )

-- #eval infer_collapse [: :] 


-- testing below
-- TODO: factor out into separate file
-- ν

#eval [: Z.0 :]
#eval [: Z.0 :]

--     ∃ 2 :: l ~ Z.0 ; r ~ Z.1 ≤ Z.3 .
--       l ~ succ^Z.0 ; r ~ cons^Z.1  |
--     (∃ 2 :: l ~ Z.0 ; r ~ Z.1 ≤ Z.3 .
--       l ~ succ^Z.0 ; r ~ cons^Z.1)
#eval [: 
    ∃ 2 :: l ~ Z.0 ; r ~ Z.1 ≤ Z.3 .
      l ~ succ^Z.0 ; r ~ cons^Z.1  |
    (∃ 2 :: l ~ Z.0 ; r ~ Z.1 ≤ Z.3 .
      l ~ succ^Z.0 ; r ~ cons^Z.1)
:]

#check [: Z.0 | X.0 :]
#check [: Z.0 ; X.0 :]
#check [: Z.0 × X.0 :]
#check [: Z.0 + X.0 :]
def x := 0
#check [: ∀ 1 :: Z.0 ≤ X.0 . Z.⟨x⟩ :]
#check [: ∀ 1 :: Z.0 ≤ X.0 . Z.0 :]
#check [: ∀ 2 :: X.0 ≤ X.0 . Z.0 :]
#check [: ∀ 2 . Z.0 :]
#check [: @ :]
#check [: X.24 :]
#check [: foo^@ | boo^@ :]
#check [: μ Z.0 . foo^Z.0 :]
#check [: μ Z.0 . foo^Z.0  ; X.0 | X.2 ; X.0:]
#check [: Z.3 ; X.0 -> X.1 | X.2 :]
#check [: μ Z.0 . foo^Z.0 ; X.0 | X.2 ; X.0 -> X.1 | X.2 :]
#check [: μ Z.0 . foo^Z.0 ; X.0 | X.2 ; X.0 :]
#check [: X.0 :]

#eval [: ∀ 2 :: X.0 ≤ X.0 . Z.0 :]
#eval [: μ Z.0 . foo^Z.0 ; X.0 | X.2 ; X.0 :]


#eval ({} : PHashMap Nat Ty)

def zero_ := [: 
    zero^@
:]

#eval (unify 3 {} [:
    (dumb^@)
:] zero_)

#eval unify 3 {} [:
    (zero^@)
:] zero_

/-
  μ nat .
    zero^@ | 
    succ^nat 
-/
def nat_ := [: 
  μ Z.0 . 
    zero^@ |
    succ^Z.0
:]
#eval nat_

def even := [: 
  μ Z.0 . 
    zero^@ |
    succ^succ^Z.0
:]

#eval unify 3 {} even nat_ 
#eval unify 3 {} nat_ even

#eval unify 3 {} [:
    (zero^@)
:] nat_ 

#eval unify 3 {} [:
    (succ^(zero^@))
:] nat_ 

#eval unify 3 {} [:
    (succ^(X.0))
:] nat_ 

def nat_list := [: 
  μ Z.0 .
    l ~ zero^@ ; r ~ nil^@ |
    ∃ 2 :: l ~ Z.0 ; r ~ Z.1 ≤ Z.2 .
      l ~ succ^Z.0 ; r ~ cons^Z.1
:]

#eval unify 3 {} 
  [: (l ~ zero^@ ; r ~ nil^@) :] 
  nat_list

#eval unify 3 {} 
  [: (l ~ zero^@ ; r ~ dumb^@) :] 
  nat_list

-- this is record type is not wellformed 
#eval unify 3 {} 
  [: (l ~ X.0 ; r ~ X.1) :] 
  nat_list

#eval unify 3 {} 
  [: (l ~ zero^@ ; r ~ X.0) :] 
  nat_list

-- #eval unify 3 [] 
--   [: (l ~ succ^zero^@ ; .r X.0 ; .g /scooby @) :] 
--   [: (l ~ succ^zero^@ ; .r /ooga @ ; .g /scooby @) | (l ~ zero^@ ; r ~ /booga @) :] 


-- expected X.0 → /nil
#eval unify 3 {} 
  [: (l ~ succ^zero^@ ; r ~ cons^X.0) :] 
  nat_list

#eval unify 3 {} 
  [: (l ~ succ^succ^zero^@ ; r ~ cons^X.0) :] 
  nat_list


def examp1 := unify 3 {} 
  [: (l ~ succ^succ^zero^@ ; r ~ cons^X.0) :] 
  nat_list

#eval Ty.collapse 10 {} examp1 [: X.0 :] 

#eval unify_collapse 3 {} 
  [: (l ~ succ^succ^zero^@ ; r ~ cons^X.0) :] 
  nat_list
  [: X.0:]

-- #eval unify 3 {} 
--   [: (.l succ^zero^@ ; .r X.0) :] 
--   nat_list

#eval unify 3 {} 
  [: (l ~ succ^zero^@ ; r ~ cons^cons^X.0) :] 
  nat_list


-- #eval unify 3 [] 
--   [: (l ~ succ^zero^@ ; r ~ cons^X.0) :] 
--   [: 
--       ∃ 2 :: l ~ Z.0 ; r ~ Z.1 ≤ (μ Z.0 .
--         l ~ zero^@ ; r ~ nil^@ |
--         ∃ 2 :: l ~ Z.0 ; r ~ Z.1 ≤ Z.2 .
--           l ~ succ^Z.0 ; r ~ cons^Z.1
--       ) .
--         l ~ succ^Z.0 ; r ~ cons^Z.1
--   :]

-- #eval unify_all 3 [
--   ([: (l ~ succ^zero^@ ; r ~ cons^X.0) :], [: l ~ succ^X.33 ; r ~ cons^X.44 :])
-- ]

-- #eval unify_all 3 [
--   ([: (l ~ succ^zero^@ ; r ~ cons^X.0) :], [: l ~ succ^X.33 ; r ~ cons^X.44 :]),
--   (
--     [: l ~ X.33 ; r ~ X.44  :], 
--     [:μ Z.0 .
--         l ~ zero^@ ; r ~ nil^@ |
--         ∃ 2 :: l ~ Z.0 ; r ~ Z.1 ≤ Z.2 .
--           l ~ succ^Z.0 ; r ~ cons^Z.1
--     :]
--   )
-- ]

/-
  μ plus .
    ∃ N .  
      zero^@ × N × N | 

    ∃ X Y Z :: X, Y, Z ≤ plus .  
      succ^X × Y × succ^Z
-/
def plus := [: 
  μ Z.0 . 
    (∃ 1 . 
      (x ~ zero^@ ; y ~ Z.0 ; z ~ Z.0)) |

    (∃ 3 :: (x ~ Z.0 ; y ~ Z.1 ; z ~ Z.2) ≤ Z.3 .   
      (x ~ succ^Z.0 ; y ~ Z.1 ; z ~ succ^Z.2))
:]

-- /print plus

-- #eval [: (x ~ zero^@ ; y ~ zero^@ ; z ~ zero^@) :]  
-- #eval [: succ^succ^zero^@ :]  


#eval unify 3 {} [:
    x ~ zero^@ ;
    y ~ X.0 ;
    z ~ zero^@
:] plus


#eval unify 3 {} [:
  (
    x ~ (succ^zero^@) ;
    y ~ (succ^zero^@) ;
    z ~ (X.0)
  )
:] plus

#eval unify_collapse 3 {} [:
  (
    x ~ (succ^zero^@) ;
    y ~ (succ^zero^@) ;
    z ~ (X.0)
  )
:] plus 
[: X.0 :]

#eval unify_collapse 3 {} [:
  (
    x ~ (succ^succ^zero^@) ;
    y ~ (succ^zero^@) ;
    z ~ (X.0)
  )
:] plus
[: X.0 :]

#eval unify_collapse 3 {} [:
  (
    x ~ (succ^zero^@) ;
    y ~ (X.0) ;
    z ~ (succ^succ^zero^@)
  )
:] plus
[: X.0 :]

-- #eval unify 3 [] [:
--   (
--     x ~ (succ^zero^@) ;
--     y ~ (succ^succ^zero^@) ;
--     z ~ (X.0)
--   )
-- :] plus

#eval unify_collapse 3 {} [:
(
  x ~ succ^zero^@ ;
  y ~ X.0 ;
  z ~ succ^succ^zero^@
)
:] plus
[: X.0 :]

-- #eval unify 3 [] [:
--   (
--     x ~ (succ^zero^@) ;
--     y ~ (X.0) ;
--     z ~ (succ^(succ^succ^(zero^@)))
--   )
-- :] plus

#eval unify_collapse 3 {} [:
(
  x ~ (X.0) ;
  y ~ (X.1) ;
  z ~ (succ^zero^@)
)
:] plus
[: x ~ X.0 ; y ~ X.1 :]

-- #eval unify 3 [] [:
--   (
--     x ~ (succ^zero^@) ;
--     y ~ (X.0) ;
--     z ~ (X.1)
--   )
-- :] plus

-- #eval unify 3 [] [:
--   (
--     x ~ (X.0) ; -- zero ; succ zero
--     y ~ (succ^zero^@) ;
--     z ~ (X.1) -- succ zero ; zero
--   )
-- :] plus


-- term testing
#eval [:
  F[ 
    for z.0 : X.0 => z.0,
    for z.0 : X.0 => z.0 
  ]
:]

#eval [:
  R[ 
    left := x.0,
    right := x.0
  ]
:]


#eval [:
  succ/zero/()
:]

#eval infer_collapse [:
  succ/zero/()
:]

#eval [:
  succ/zero/()
:]