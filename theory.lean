import Init.Data.Hashable
import Lean.Data.AssocList
import Lean.Data.PersistentHashMap


open Lean PersistentHashMap
open Std

partial def multi_step {T : Type} [BEq T] (step : T -> T) (source : T): T :=
  let sink := step source 
  if sink == source then
    sink
  else 
    multi_step step sink


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


inductive Ty : Type
| bvar : Nat -> Ty  
| fvar : Nat -> Ty
| unit : Ty
| bot : Ty
| top : Ty
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
#check List.repr

protected partial def Ty.repr (ty : Ty) (n : Nat) : Format :=
match ty with
| .bvar id => 
  "β[" ++ repr id ++ "]"
| .fvar id =>
  "α[" ++ repr id ++ "]"
| .unit => "@" 
| .bot => "⊥" 
| .top => "⊤" 
| .tag l ty1 => 
  (l ++ "^" ++ (Ty.repr ty1 n))
| .field l ty1 => 
  (l ++ " ~ " ++ (Ty.repr ty1 n))

| .union (Ty.tag "inl" inl) (Ty.tag "inr" inr) =>
  Format.bracket "(" ((Ty.repr inl n) ++ " +" ++ Format.line ++ (Ty.repr inr n)) ")"
| .union ty1 ty2 =>
  let _ : ToFormat Ty := ⟨fun ty' => Ty.repr ty' n ⟩
  let tys := [ty1, ty2] 
  Format.joinSep tys (" |" ++ Format.line)

| .inter (Ty.field "l" l) (Ty.field "r" r) =>
  Format.bracket "(" ((Ty.repr l n) ++ " × " ++ (Ty.repr r n)) ")"
| .inter ty1 ty2 =>
  Format.bracket "(" ((Ty.repr ty1 n) ++ " ; " ++ (Ty.repr ty2 n)) ")"
| .case ty1 ty2 =>
  Format.bracket "(" ((Ty.repr ty1 n) ++ " ->" ++ Format.line ++ (Ty.repr ty2 n)) ")"
| .univ n ty_c1 ty_c2 ty_pl =>
  "∀ " ++ (repr n) ++ " :: " ++
  (Ty.repr ty_c1 n) ++ " ≤ " ++ (Ty.repr ty_c2 n) ++ " =>" ++ Format.line ++ 
  (Ty.repr ty_pl n)
| .exis n ty_c1 ty_c2 ty_pl =>
  "∃ " ++ (repr n) ++ " :: " ++
  (Ty.repr ty_c1 n) ++ " ≤ " ++ (Ty.repr ty_c2 n) ++ " =>" ++ Format.line ++ 
  (Ty.repr ty_pl n)
| .recur ty1 =>
  "μ β[0] => " ++ (Ty.repr ty1 n)
| .corec ty1 =>
  "ν β[0] => " ++ (Ty.repr ty1 n)

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
  "y[" ++ repr id ++ "]"
| .fvar id => 
  "x[" ++ repr id ++ "]"
| .tag l t1 =>
  l ++ "#" ++ (Tm.repr t1 n)
| record [("l", l), ("r", r)] =>
  let _ : ToFormat Tm := ⟨fun t1 => Tm.repr t1 n ⟩
  Format.bracket "(" (Format.joinSep [l, r] ("," ++ Format.line)) ")"
| record fds =>
  let _ : ToFormat (String × Tm) := ⟨fun (l, t1) =>
    l ++ " := " ++ Tm.repr t1 n ⟩
  "ω" ++ Format.bracket "[" (Format.joinSep fds ("," ++ Format.line)) "]"
| func [(pat, op_ty_pat, tb)] =>
  match op_ty_pat with
  | .some ty_pat =>
    "λ " ++ (Tm.repr pat n) ++ " : " ++ (Ty.repr ty_pat n) ++ 
    " => " ++ (Tm.repr tb (n))
  | .none =>
    "λ " ++ (Tm.repr pat n) ++ " => " ++ (Tm.repr tb (n))
| func fs =>
  let _ : ToFormat (Tm × Option Ty × Tm) := ⟨fun (pat, op_ty_pat, tb) =>
    match op_ty_pat with
    | .some ty_pat =>
      "for " ++ (Tm.repr pat n) ++ " : " ++ (Ty.repr ty_pat n) ++ 
      " => " ++ (Tm.repr tb (n))
    | .none =>
      "for " ++ (Tm.repr pat n) ++ " => " ++ (Tm.repr tb (n))
  ⟩
  "λ" ++ Format.bracket "[" (Format.joinSep fs ("," ++ Format.line)) "]"
| .proj t1 l =>
  Tm.repr t1 n ++ "/" ++ l
| .app t1 t2 =>
  Format.bracket "(" (Tm.repr t1 n) ") " ++ "(" ++ Tm.repr t2 n ++ ")"
| .letb op_ty1 t1 t2 =>
  match op_ty1 with
  | .some ty1 =>
    "let y[0] : " ++ (Ty.repr ty1 n) ++ " = " ++  (Tm.repr t1 n) ++ " =>" ++
    Format.line  ++ (Tm.repr t2 n) 
  | .none =>
    "let y[0] = " ++  (Tm.repr t1 n) ++ " =>" ++
    Format.line  ++ (Tm.repr t2 n) 
| .fix t1 =>
  Format.bracket "(" ("fix " ++ (Tm.repr t1 n)) ")"


instance : Repr Tm where
  reprPrec := Tm.repr


declare_syntax_cat slm
syntax:100 num : slm 
syntax:100 ident : slm
syntax "[" slm,+ "]" : slm 
-- type
syntax:90 "β["slm:100"]" : slm
syntax:90 "α["slm:100"]" : slm
syntax:90 "@" : slm
syntax:90 "⊥" : slm
syntax:90 "⊤" : slm
syntax:90 slm:100 "^" slm:90 : slm
syntax:90 slm:100 "~" slm:90 : slm
syntax:50 slm:51 "->" slm:50 : slm
syntax:60 slm:60 "|" slm:61 : slm
syntax:60 slm:60 "+" slm:61 : slm
syntax:70 slm:70 ";" slm:71 : slm
syntax:70 slm:70 "×" slm:71 : slm
syntax:40 "∃" slm "::" slm "≤" slm "=>" slm:40 : slm 
syntax:40 "∃" slm "=>" slm:40 : slm 
syntax:40 "∀" slm "::" slm "≤" slm "=>" slm:40 : slm 
syntax:40 "∀" slm "=>" slm:40 : slm 
syntax:80 "μ β[0] =>" slm : slm 
syntax:80 "ν β[0] =>" slm : slm 

--term
syntax:30 "_" : slm
syntax:30 "()" : slm
syntax:30 "y[" slm:90 "]": slm
syntax:30 "x[" slm:90 "]" : slm
syntax:30 slm:100 "#" slm:30 : slm
syntax:30 slm:100 ":=" slm:30 : slm
syntax:30 "(" slm "," slm ")" : slm
syntax:30 "ω" slm : slm
syntax:20 "for" slm:30 ":" slm "=>" slm:20 : slm 
syntax:20 "for" slm:30 "=>" slm:20 : slm 
syntax:20 "λ" slm:30 ":" slm "=>" slm:20 : slm 
syntax:20 "λ" slm:30 "=>" slm:20 : slm 
syntax:30 "λ" slm : slm 
syntax:30 slm:30 "/" slm:100 : slm 
syntax:30 "(" slm:30 slm:30 ")" : slm 
syntax:30 "let y[0]" ":" slm:30 "=" slm:30 "=>" slm:30 : slm 
syntax:30 "let y[0]" "=" slm:30 "=>" slm:30 : slm 
syntax:30 "fix " slm:30 : slm 

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
| `([: β[$n] :]) => `(Ty.bvar [: $n :])
| `([: α[$n:slm] :]) => `(Ty.fvar [: $n :])
| `([: @ :]) => `(Ty.unit)
| `([: ⊥ :]) => `(Ty.bot)
| `([: ⊤ :]) => `(Ty.top)
| `([: $a ^ $b:slm :]) => `(Ty.tag [: $a :] [: $b :])
| `([: $a ~ $b:slm :]) => `(Ty.field [: $a :] [: $b :])
| `([: $a -> $b :]) => `(Ty.case [: $a :] [: $b :])
| `([: $a | $b :]) => `(Ty.union [: $a :] [: $b :])
| `([: $a + $b :]) => `(Ty.union (Ty.tag "inl" [: $a :]) (Ty.tag "inr" [: $b :]))
| `([: $a ; $b :]) => `(Ty.inter [: $a :] [: $b :])
| `([: $a × $b :]) => `(Ty.inter (Ty.field "l" [: $a :]) (Ty.field "r" [: $b :]))
| `([: ∀ $a :: $b ≤ $c => $d :]) => `(Ty.univ [: $a :] [: $b :] [: $c :] [: $d :])
| `([: ∀ $a:slm => $b:slm :]) => `(Ty.univ [: $a :] [: ⊥ :] [: ⊤ :] [: $b :] )
| `([: ∃ $a :: $b ≤ $c => $d  :]) => `(Ty.exis [: $a :] [: $b :] [: $c :] [: $d :])
| `([: ∃ $a:slm => $b:slm :]) => `(Ty.exis [: $a :] [: ⊥ :] [: ⊤ :] [: $b :] )
| `([: μ β[0] => $a :]) => `(Ty.recur [: $a :])
| `([: ν β[0] => $a :]) => `(Ty.corec [: $a :])
--Tm
| `([: _ :]) => `(Tm.hole)
| `([: () :]) => `(Tm.unit)
| `([: y[$n] :]) => `(Tm.bvar [: $n :])
| `([: x[$n] :]) => `(Tm.fvar [: $n :])
| `([: $a # $b :]) => `(Tm.tag [: $a :] [: $b :])
| `([: $a := $b :]) => `(([: $a :], [: $b :]))
| `([: for $b : $c => $d :]) => `(([: $b :], Option.some [: $c :], [: $d :]))
| `([: for $b => $d :]) => `(([: $b :], Option.none, [: $d :]))
| `([: ω $a :]) => `(Tm.record [: $a :])
| `([: ( $a , $b ) :]) => `(Tm.record [("l", [: $a :]), ("r", [:$b :])])
| `([: λ $b : $c => $d :]) => `(Tm.func [([: $b :], Option.some [: $c :], [: $d :])])
| `([: λ $b => $d :]) => `(Tm.func [([: $b :], Option.none, [: $d :])])
| `([: λ $a :]) => `(Tm.func [: $a :])
| `([: $a / $b :]) => `(Tm.proj [: $a :] [: $b :])
| `([: ($a $b) :]) => `(Tm.app [: $a :] [: $b :])
| `([: let y[0] : $a = $b => $c :]) => `(Tm.letb (Option.some [: $a :]) [: $b :] [: $c :])
| `([: let y[0] = $b => $c :]) => `(Tm.letb Option.none [: $b :] [: $c :])
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


partial def Ty.subst (m : PHashMap Nat Ty) : Ty -> Ty
| .bvar id => .bvar id 
| .fvar id => (match m.find? id with
  | some ty => Ty.subst m ty 
  | none => .fvar id
)
| .unit => .unit
| .bot => .bot
| .top => .top
| .tag l ty => .tag l (Ty.subst m ty) 
| .field l ty => .field l (Ty.subst m ty)
| .union ty1 ty2 => .union (Ty.subst m ty1) (Ty.subst m ty2)
| .inter ty1 ty2 => .inter (Ty.subst m ty1) (Ty.subst m ty2)
| .case ty1 ty2 => .case (Ty.subst m ty1) (Ty.subst m ty2)
| .exis n ty_c1 ty_c2 ty => (.exis n
  (Ty.subst m ty_c1) (Ty.subst m ty_c2) 
  (Ty.subst m ty)
)
| .univ n ty_c1 ty_c2 ty => (.univ n 
  (Ty.subst m ty_c1) (Ty.subst m ty_c2)
  (Ty.subst m ty)
)
| .recur ty => .recur (Ty.subst m ty)
| .corec ty => .corec (Ty.subst m ty)

partial def Ty.simplify : Ty -> Ty
| .bvar id => Ty.bvar id  
| .fvar id => Ty.fvar id 
| .unit => .unit 
| .bot => .bot 
| .top => .top 
| .tag l ty => Ty.tag l (Ty.simplify ty) 
| .field l ty => Ty.field l (Ty.simplify ty) 
| .union ty1 ty2 =>
  let ty1' := Ty.simplify ty1
  let ty2' := Ty.simplify ty2
  if ty1' == Ty.top || ty2' == Ty.top then 
    Ty.top 
  else if ty1' == ty2' || ty2' == Ty.bot then 
    ty1'
  else if ty1' == Ty.bot then 
    ty2'
  else
    Ty.union ty1' ty2'

| .inter ty1 ty2 =>
  let ty1' := Ty.simplify ty1
  let ty2' := Ty.simplify ty2
  if ty1' == Ty.bot || ty2' == Ty.bot then 
    Ty.bot 
  else if ty1' == ty2' || ty2' == Ty.top then 
    ty1'
  else if ty1' == Ty.top then 
    ty2'
  else
    Ty.inter ty1' ty2'

| .case ty1 ty2 => Ty.case (Ty.simplify ty1) (Ty.simplify ty2)
| .exis n cty1 cty2 ty => 
    Ty.exis n  
      (Ty.simplify cty1) (Ty.simplify cty2)
      (Ty.simplify ty)
| .univ n cty1 cty2 ty => 
    Ty.univ n  
      (Ty.simplify cty1) (Ty.simplify cty2)
      (Ty.simplify ty)
| .recur ty => Ty.recur (Ty.simplify ty)
| .corec ty => Ty.corec (Ty.simplify ty)




declare_syntax_cat sub
syntax slm "//" slm : sub 
syntax "[" sub,+ "]" : sub
syntax "[sub:" sub ":]" : term 

macro_rules
  | `([sub: $a:slm // $b:slm :]) => `(([: $a :], [: $b :])) 

macro_rules
  | `([sub: [$x:sub] :]) => `([ [sub: $x :] ])
  | `([sub: [$x,$xs:sub,*] :]) => `([sub: $x :] :: [sub: [$xs,*] :])


-- syntax slm "%" sub : slm 
-- macro_rules
--   | `([: $a % $b:sub :]) => `(Ty.subst (PHashMap.from_list [sub: $b :]) [: $a :])


-- #check [: (β[1]) % [1 // α[0]] :]
-- #check [: (β[1]) % [1//α[0]] :]



def Ty.free_vars : Ty -> PHashMap Nat Unit
| .bvar id => {} 
| .fvar id => 
  let u : Unit := Unit.unit
  PHashMap.from_list [(id, u)] 
| .unit => {} 
| .bot => {} 
| .top => {} 
| .tag l ty => (Ty.free_vars ty) 
| .field l ty => (Ty.free_vars ty)
| .union ty1 ty2 => Ty.free_vars ty1 ;; Ty.free_vars ty2
| .inter ty1 ty2 => Ty.free_vars ty1 ;; Ty.free_vars ty2
| .case ty1 ty2 => Ty.free_vars ty1 ;; Ty.free_vars ty2
| .univ n ty_c1 ty_c2 ty => 
  (Ty.free_vars ty_c1);;(Ty.free_vars ty_c2);;(Ty.free_vars ty)
| .exis n ty_c1 ty_c2 ty =>
  (Ty.free_vars ty_c1);;(Ty.free_vars ty_c2);;(Ty.free_vars ty)
| .recur ty => (Ty.free_vars ty)
| .corec ty => (Ty.free_vars ty)


def Ty.generalize (fids : List Nat) (start : Nat) : Ty -> Ty
| .bvar id => .bvar id 
| .fvar id => 
  match (fids.enumFrom start).find? (fun (_, fid) => fid == id) with
  | .some (bid, _) => .bvar bid
  | .none => .fvar id 
| .unit => .unit
| .bot => .bot
| .top => .top
| .tag l ty => .tag l (Ty.generalize fids start ty) 
| .field l ty => .field l (Ty.generalize fids start ty)
| .union ty1 ty2 => .union (Ty.generalize fids start ty1) (Ty.generalize fids start ty2)
| .inter ty1 ty2 => .inter (Ty.generalize fids start ty1) (Ty.generalize fids start ty2)
| .case ty1 ty2 => .case (Ty.generalize fids start ty1) (Ty.generalize fids start ty2)
| .univ n ty_c1 ty_c2 ty => (.univ n
  (Ty.generalize fids (start + n) ty_c1) (Ty.generalize fids (start + n) ty_c2)
  (Ty.generalize fids (start + n) ty)
)
| .exis n ty_c1 ty_c2 ty => (.exis n
  (Ty.generalize fids (start + n) ty_c1) (Ty.generalize fids (start + n) ty_c2)
  (Ty.generalize fids (start + n) ty)
)
| .recur ty => .recur (Ty.generalize fids (start + 1) ty)
| .corec ty => .corec (Ty.generalize fids (start + 1) ty)


def Ty.instantiate (start : Nat) (args : List Ty) : Ty -> Ty
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
| .bot => .bot
| .top => .top
| .tag l ty => .tag l (Ty.instantiate start args ty) 
| .field l ty => .field l (Ty.instantiate start args ty)
| .union ty1 ty2 => .union (Ty.instantiate start args ty1) (Ty.instantiate start args ty2)
| .inter ty1 ty2 => .inter (Ty.instantiate start args ty1) (Ty.instantiate start args ty2)
| .case ty1 ty2 => .case (Ty.instantiate start args ty1) (Ty.instantiate start args ty2)
| .univ n ty_c1 ty_c2 ty => (.univ n
  (Ty.instantiate (start + n) args ty_c1) (Ty.instantiate (start + n) args ty_c2)
  (Ty.instantiate (start + n) args ty)
)
| .exis n ty_c1 ty_c2 ty => (.exis n
  (Ty.instantiate (start + n) args ty_c1) (Ty.instantiate (start + n) args ty_c2)
  (Ty.instantiate (start + n) args ty)
)
| .recur ty => .recur (Ty.instantiate (start + 1) args ty)
| .corec ty => .corec (Ty.instantiate (start + 1) args ty)

syntax slm "↑" slm "//" slm : slm 

macro_rules
  | `([: $a ↑ $b // $c :]) => `(Ty.instantiate [: $b :] [: $c :] [: $a :])


def τ := [: α[0] :]
#check [: ⟨τ⟩ ↑ 0 // [μ β[0] => ⟨τ⟩]:]




partial def unroll : Ty -> Ty
| .recur ty => 
  -- Ty.instantiate 0 [Ty.recur τ] τ 
  [: ⟨ty⟩ ↑ 0 // [μ β[0] => ⟨ty⟩]:]
| .corec ty => 
  -- Ty.instantiate 0 [Ty.corec τ] τ 
  [: ⟨ty⟩ ↑ 0 // [ν β[0] => ⟨ty⟩]:]
| ty => ty


partial def roll_recur (key : Nat) (m : PHashMap Nat Ty) (ty : Ty) : Ty :=
  let ty := Ty.subst m ty  
  if (Ty.free_vars ty).contains key then
    Ty.subst (PHashMap.from_list [(key, [: β[0] :])]) [: (μ β[0] => ⟨ty⟩) :] 
  else
    ty 

partial def roll_corec (key : Nat) (m : PHashMap Nat Ty) (ty : Ty) : Ty :=
  let ty := Ty.subst m ty
  if (Ty.free_vars ty).contains key then
    Ty.subst (PHashMap.from_list [(key, [: β[0] :])]) [: (ν β[0] => ⟨ty⟩) :] 
  else
    ty


partial def Ty.subst_default (sign : Bool) : Ty -> Ty
| .bvar id => Ty.bvar id  
| .fvar _ => if sign then Ty.bot else Ty.top
| .unit => .unit 
| .bot => .bot 
| .top => .top 
| .tag l ty => Ty.tag l (Ty.subst_default sign ty) 
| .field l ty => Ty.field l (Ty.subst_default sign ty) 
| .union ty1 ty2 =>
  Ty.union (Ty.subst_default sign ty1) (Ty.subst_default sign ty2)
| .inter ty1 ty2 =>
  Ty.inter (Ty.subst_default sign ty1) (Ty.subst_default sign ty2)
| .case ty1 ty2 => Ty.case (Ty.subst_default (!sign) ty1) (Ty.subst_default sign ty2)
| .univ n cty1 cty2 ty => 
    Ty.univ n  
      (Ty.subst_default True cty1) (Ty.subst_default False cty2)
      (Ty.subst_default sign ty)
| .exis n cty1 cty2 ty => 
    Ty.exis n  
      (Ty.subst_default True cty1) (Ty.subst_default False cty2)
      (Ty.subst_default sign ty)
| .recur ty => Ty.recur (Ty.subst_default sign ty)
| .corec ty => Ty.corec (Ty.subst_default sign ty)


partial def Ty.equal (env_ty : PHashMap Nat Ty) (ty1 : Ty) (ty2 : Ty) : Bool :=
  let ty1 := Ty.simplify (Ty.subst env_ty ty1)
  let ty2 := Ty.simplify (Ty.subst env_ty ty2)
  ty1 == ty2

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



def wellformed_record_type (env_ty : PHashMap Nat Ty) (ty : Ty) : Bool :=
  match linearize_fields (Ty.simplify (Ty.subst env_ty ty)) with
  | .some fields => 
    List.any fields (fun (k_fd, ty_fd) =>
      match ty_fd with
      | .fvar _ => false 
      | _ => true 
    ) 
  | .none => false


partial def unify (i : Nat) (env_ty : PHashMap Nat Ty) (closed : Bool): 
Ty -> Ty -> List (Nat × PHashMap Nat Ty)
| (.fvar id1), (.fvar id2) => 
  match (env_ty.find? id1, env_ty.find? id2) with 
  | (.none, .none) => 
    [
      (i, PHashMap.from_list [
        (id1, Ty.fvar id2)
      ])
    ]
  | (_, .some ty) => unify i env_ty closed (.fvar id1) ty 
  | (.some ty', _) => unify i env_ty closed ty' (.fvar id2) 

| .fvar id, ty  => 
  match env_ty.find? id with 
  | none => 
    [ 
      if closed then
        (i, PHashMap.from_list [
          (id, roll_recur id env_ty ty)
        ]) 
      else
        (i + 1, PHashMap.from_list [
          (id, Ty.inter (roll_recur id env_ty ty) (Ty.fvar i))
        ]) 
    ]
  | some ty' => unify i env_ty closed ty' ty 

| ty', .fvar id  => match env_ty.find? id with 
  | none => 
    [ 
      if closed then
        (i, PHashMap.from_list [
          (id, roll_corec id env_ty ty')
        ]) 
      else
        (i + 1, PHashMap.from_list [
          (id, Ty.union (roll_corec id env_ty ty') (Ty.fvar i))
        ]) 
    ]
  | some ty => unify i env_ty closed ty' ty 

| .bvar id1, .bvar id2  =>
  if id1 = id2 then 
    [ (i, {}) ]
  else
    .nil

| .bot, _ => [ (i, {}) ] 
| _, .top => [ (i, {}) ] 
| .unit, .unit => [ (i, {}) ] 

| .tag l' ty', .tag l ty =>
  if l' = l then
    unify i env_ty closed ty' ty
  else
    .nil 

| .field l' ty', .field l ty =>
  if l' = l then
    unify i env_ty closed ty' ty
  else
    .nil

| .case ty1 ty2', .case ty1' ty2 =>
  List.bind (unify i env_ty closed ty1' ty1) (fun (i, env_ty1) => 
  List.bind (unify i (env_ty ;; env_ty1) closed ty2' ty2) (fun (i, env_ty2) =>
    [ (i, env_ty1 ;; env_ty2) ]
  ))


| .exis n1 ty_c1 ty_c2 ty1, .exis n2 ty_c3 ty_c4 ty2 =>
  let (i, args1) := (i + n1, (List.range n1).map (fun j => Ty.fvar (i + j)))
  let ty_c1 := Ty.instantiate 0 args1 ty_c1
  let ty_c2 := Ty.instantiate 0 args1 ty_c2
  let ty1 := Ty.instantiate 0 args1 ty1

  let (i, args2) := (i + n2, (List.range n1).map (fun j => Ty.fvar (i + j)))
  let ty_c3 := Ty.instantiate 0 args2 ty_c3
  let ty_c4 := Ty.instantiate 0 args2 ty_c4
  let ty2 := Ty.instantiate 0 args2 ty2

  List.bind (unify i (env_ty) closed ty1 ty2) (fun (i, env_ty1) =>
  List.bind (unify i (env_ty;;env_ty1) True ty_c3 ty_c4) (fun (i, env_ty2) =>

  -- unify with LHS constraints narrower than RHS constraints 
  List.bind (unify i (env_ty;;env_ty1;;env_ty2) True ty_c3 ty_c1) (fun (i, env_ty3) =>
  List.bind (unify i (env_ty;;env_ty1;;env_ty2;;env_ty3) True ty_c1 ty_c2) (fun (i, env_ty4) =>
  List.bind (unify i (env_ty;;env_ty1;;env_ty2;;env_ty3;;env_ty4) True ty_c2 ty_c4) (fun (i, env_ty5) =>

    [ (i, env_ty1;;env_ty2;;env_ty3;;env_ty4;;env_ty5)  ]
  )))))

| ty', .exis n ty_c1 ty_c2 ty =>
  let (i, args) := (i + n, (List.range n).map (fun j => .fvar (i + j)))

  let ty_c1 := Ty.instantiate 0 args ty_c1
  let ty_c2 := Ty.instantiate 0 args ty_c2
  let ty := Ty.instantiate 0 args ty
  List.bind (unify i env_ty closed ty' ty) (fun (i, env_ty1) =>
  List.bind (unify i (env_ty ;; env_ty1) True ty_c1 ty_c2) (fun (i, env_ty2) => 
    [ (i, env_ty1 ;; env_ty2) ]
  ))

| .univ n1 ty_c1 ty_c2 ty1, .univ n2 ty_c3 ty_c4 ty2 =>
  let (i, args1) := (i + n1, (List.range n1).map (fun j => Ty.fvar (i + j)))
  let ty_c1 := Ty.instantiate 0 args1 ty_c1
  let ty_c2 := Ty.instantiate 0 args1 ty_c2
  let ty1 := Ty.instantiate 0 args1 ty1

  let (i, args2) := (i + n2, (List.range n1).map (fun j => Ty.fvar (i + j)))
  let ty_c3 := Ty.instantiate 0 args2 ty_c3
  let ty_c4 := Ty.instantiate 0 args2 ty_c4
  let ty2 := Ty.instantiate 0 args2 ty2

  List.bind (unify i (env_ty) closed ty1 ty2) (fun (i, env_ty1) =>
  List.bind (unify i (env_ty;;env_ty1) True ty_c1 ty_c2) (fun (i, env_ty2) =>

  -- unify with LHS constraints wider than RHS constraints 
  List.bind (unify i (env_ty;;env_ty1;;env_ty2) True ty_c1 ty_c3) (fun (i, env_ty3) =>
  List.bind (unify i (env_ty;;env_ty1;;env_ty2;;env_ty3) True ty_c3 ty_c4) (fun (i, env_ty4) =>
  List.bind (unify i (env_ty;;env_ty1;;env_ty2;;env_ty3;;env_ty4) True ty_c4 ty_c2) (fun (i, env_ty5) =>
    [ (i, env_ty1;;env_ty2;;env_ty3;;env_ty4;;env_ty5)  ]
  )))))

| .univ n ty_c1 ty_c2 ty', ty =>
  let (i, args) := (i + n, (List.range n).map (fun j => .fvar (i + j)))
  let ty_c1 := Ty.instantiate 0 args ty_c1
  let ty_c2 := Ty.instantiate 0 args ty_c2
  let ty' := Ty.instantiate 0 args ty'
  List.bind (unify i env_ty closed ty' ty) (fun (i, env_ty1) =>
  List.bind (unify i (env_ty ;; env_ty1) True ty_c1 ty_c2) (fun (i, env_ty2) => 
    [ (i, env_ty1 ;; env_ty2) ]
  ))

| .recur ty', .recur ty =>
  if Ty.equal env_ty ty' ty then
    [ (i, {}) ]
  else
    let ty' := [: ⟨ty'⟩ ↑ 0 // [μ β[0] => ⟨ty⟩]:]
    let ty := [: ⟨ty⟩ ↑ 0 // [μ β[0] => ⟨ty⟩]:]
    unify i env_ty closed ty' ty

| .tag l ty', .recur ty =>
  unify i env_ty closed (.tag l ty') (unroll (.recur ty))


| ty', .recur ty =>
  if wellformed_record_type env_ty ty' then 
    unify i env_ty closed ty' (unroll (Ty.recur ty))
  else
    .nil

| .corec ty', .corec ty =>
  if Ty.equal env_ty ty' ty then
    [ (i, {}) ]
  else
    let ty' := [: ⟨ty'⟩ ↑ 0 // [ν β[0] => ⟨ty'⟩] :]
    let ty := [: ⟨ty⟩ ↑ 0 // [ν β[0] => ⟨ty'⟩] :]
    unify i env_ty closed ty' ty


-- TODO: determine if wellformed check is needed to always converge
| .corec ty_corec, Ty.case ty1 ty2 =>
  unify i env_ty closed (unroll (Ty.corec ty_corec)) (Ty.case ty1 ty2)

| .union ty1 ty2, ty => 
  List.bind (unify i env_ty closed ty1 ty) (fun (i, env_ty1) => 
  List.bind (unify i (env_ty ;; env_ty1) closed ty2 ty) (fun (i, env_ty2) =>
    [ (i, env_ty1 ;; env_ty2) ]
  ))

| ty, .union ty1 ty2 => 
  (unify i env_ty closed ty ty1) ++ (unify i env_ty closed ty ty2)


| ty, .inter ty1 ty2 => 
  List.bind (unify i env_ty closed ty ty1) (fun (i, env_ty1) => 
  List.bind (unify i (env_ty ;; env_ty1) closed ty ty2) (fun (i, env_ty2) =>
    [ (i, env_ty1 ;; env_ty2) ]
  ))

| .inter ty1 ty2, ty => 
  (unify i env_ty closed ty1 ty) ++ (unify i env_ty closed ty2 ty)

| _, _ => .nil 

def unify_all (i : Nat) (cs : List (Ty × Ty)) : List (Nat × PHashMap Nat Ty) := 
  List.foldl (fun u_env_ty1 => fun (ty_c1, ty_c2) => 
    List.bind u_env_ty1 (fun (i, env_ty1) => 
    List.bind (unify i env_ty1 False ty_c1 ty_c2) (fun (i, env_ty2) =>
      [ (i, env_ty1 ;; env_ty2) ]
    ))
  ) [(i, {})] cs


def Ty.refresh (i : Nat) : Ty -> (Nat × Ty)
  | .bvar id => (i + 1, Ty.bvar id) 
  | .fvar _ => (i + 1, Ty.fvar i)
  | .unit => (i + 1, .unit) 
  | .bot => (i + 1, .bot) 
  | .top => (i + 1, .top) 
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
      (fun t' => not (t == t'))
      ts
    match Ty.union_all ts with
      | .none => .some t
      | .some t' => Ty.union t t'


partial def unify_reduce (ty1) (ty2) (ty_result) :=
  (unify 31 {} True ty1 ty2).foldl (fun acc => fun  (_, env_ty) =>
    Ty.simplify ((Ty.subst env_ty (Ty.union acc ty_result)))
  ) (Ty.bot)



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

partial def Tm.instantiate (start : Nat) (args : List Tm) : Tm -> Tm
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
| .tag l t => Tm.tag l (Tm.instantiate start args t)
| .record fds =>
  Tm.record (List.map (fun (l, t) =>
    (l, Tm.instantiate start args t)
  ) fds)
| .func fs =>
  Tm.func (List.map (fun (tp, op_ty_p, tb) =>
    let n := match pattern_wellformed 0 tp with
    | .some n => n 
    | .none => 0 
    let tp := Tm.instantiate (start + n) args tp 
    let tb := Tm.instantiate (start + n) args tb
    (tp, op_ty_p, tb)
  ) fs)
| .proj t l => 
  Tm.proj (Tm.instantiate start args t) l
| .app t1 t2 =>
  Tm.app 
    (Tm.instantiate start args t1) 
    (Tm.instantiate start args t2)
| .letb ty1 t1 t2 =>
  Tm.letb ty1 
    (Tm.instantiate start args t1)
    (Tm.instantiate (start + 1) args t2)
| .fix t =>
  Tm.fix (Tm.instantiate start args t)


def Option.toList : Option T -> List T 
| .some x => [x]
| .none => []


partial def infer (i : Nat)
(env_ty : PHashMap Nat Ty) (env_tm : PHashMap Nat Ty) (closed : Bool) (t : Tm) (ty : Ty) : 
List (Nat × (PHashMap Nat Ty) × Ty) := 
match t with
| Tm.hole => [(i, {}, ty)] 
| Tm.unit => 
  List.bind (unify i env_ty closed Ty.unit ty) (fun (i, env_ty_x) => 
    [(i, env_ty_x, Ty.unit)]
  )
| Tm.bvar _ => .nil 
| Tm.fvar id =>
  match (env_tm.find? id) with 
    | .some ty' => 
      List.bind (unify i env_ty closed ty' ty) (fun (i, env_ty_x) =>
        [(i, env_ty_x, ty')]
      )
    | .none => .nil 

| .tag l t1 =>   
  let (i, ty1) := (i + 1, .fvar i)
  List.bind (unify i env_ty closed (Ty.tag l ty1) ty) (fun (i, env_ty1) =>
  List.bind (infer i (env_ty ;; env_ty1) env_tm closed t1 ty1) (fun (i, env_ty_x, ty1') =>
    [ (i, env_ty1 ;; env_ty_x, Ty.tag l ty1') ]
  ))

| .record fds =>
  let (i, trips) := List.foldl (fun (i, ty_acc) => fun (l, t1) =>
    (i + 1, (l, t1, (Ty.fvar i)) :: ty_acc)
  ) (i, []) fds

  let ty_init := Ty.top

  let ty' := List.foldl (fun ty_acc => fun (l, _, ty1) => 
    Ty.inter (Ty.field l ty1) ty_acc 
  ) ty_init trips 

  let u_env_ty1 := unify i env_ty closed ty' ty 

  let f_step := fun acc => (fun (l, t1, ty1) =>
    List.bind acc (fun (i, env_ty_acc, ty_acc) =>
    List.bind (infer i (env_ty ;; env_ty_acc) env_tm closed t1 ty1) (fun (i, env_ty_x, ty1') =>
      [(i, env_ty_acc ;; env_ty_x, Ty.inter (Ty.field l ty1') ty_acc)]
    ))
  )

  let init := u_env_ty1.map fun (i, env_ty1) => (i, env_ty1, Ty.top)
  List.foldl f_step init trips 

| .func fs =>
  let (i, fs_typed) := List.foldl (fun (i, ty_acc) => fun (p, op_ty_p, b) =>
    (i + 1, (p, op_ty_p, b, (Ty.fvar i)) :: ty_acc)
  ) (i, []) fs

  let case_init := Ty.top

  let (i, ty') := List.foldl (fun (i, ty_acc) (p, op_ty_p, b, ty_b) => 
    let (i, ty_p) := match op_ty_p with
      | .some ty_p => (i, ty_p)
      | .none => (i + 1, Ty.fvar i)
    (i, Ty.inter (Ty.case ty_p ty_b) ty_acc) 
  ) (i, case_init) fs_typed 

  let u_env_ty1 := unify i env_ty closed ty' ty 

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

    let p := Tm.instantiate 0 list_tm_x p 
    let (i, ty_p) := match op_ty_p with
      | .some ty_p => (i, ty_p)
      | .none => (i + 1, Ty.fvar i)

    let b := Tm.instantiate 0 list_tm_x b  
    List.bind (infer i (env_ty ;; env_ty_acc) (env_tm ;; env_pat) True p ty_p) (fun (i, env_ty_p, _) =>
    List.bind (infer i (env_ty ;; env_ty_acc ;; env_ty_p) (env_tm ;; env_pat) closed b ty_b) (fun (i, env_ty_b, ty_b') =>
      [(i, env_ty_acc ;; env_ty_p ;; env_ty_b, Ty.inter (Ty.case ty_p ty_b') ty_acc)]
    ))))
  )

  let init := u_env_ty1.map fun (i, env_ty1) => (i, env_ty1, Ty.top)
  List.foldl f_step init fs_typed 


| .proj t1 l =>
  List.bind (infer i env_ty env_tm closed t1 (Ty.field l ty)) (fun (i, env_ty1, _) =>
    [(i, env_ty1, ty)]
  )

-- | .proj t1 l =>
--   List.bind (infer i env_ty env_tm closed t1 (Ty.field l ty)) (fun (i, env_ty1, ty1') =>
--   let (i, ty') := (i + 1, Ty.fvar i)
--   List.bind (unify i (env_ty ;; env_ty1) closed ty1' (Ty.field l ty')) (fun (i, env_ty2) =>
--     [(i, env_ty1 ;; env_ty2, ty')]
--   ))

| .app t1 t2 =>
  let (i, ty2) := (i + 1, Ty.fvar i)
  List.bind (infer i env_ty env_tm closed t1 (Ty.case ty2 ty)) (fun (i, env_ty1, _) =>
  List.bind (infer i (env_ty ;; env_ty1) env_tm closed t2 ty2) (fun (i, env_ty2, _) =>
     [(i, env_ty1 ;; env_ty2, ty)]
  ))

-- | .app t1 t2 =>
--   let (i, ty2) := (i + 1, Ty.fvar i)
--   let (i, ty') := (i + 1, Ty.fvar i)
--   List.bind (infer i env_ty env_tm closed t1 (Ty.case ty2 ty)) (fun (i, env_ty1, ty1) =>
--   List.bind (infer i (env_ty ;; env_ty1) env_tm closed t2 ty2) (fun (i, env_ty2, ty2') =>
--   List.bind (unify i (env_ty ;; env_ty1 ;; env_ty2) closed ty1 (Ty.case ty2' ty')) (fun (i, env_ty3) =>
--      [(i, env_ty1 ;; env_ty2 ;; env_ty3, ty')]
--   )))

| .letb op_ty1 t1 t => 
  let (i, ty1) := match op_ty1 with
    | .some ty1 => (i, ty1) 
    | .none => (i + 1, Ty.fvar i)
  List.bind (infer i env_ty env_tm closed t1 ty1) (fun (i, env_ty1, ty1') =>
  let ty1' := (Ty.subst (env_ty;;env_ty1) ty1')
  let fvs := (Ty.free_vars ty1').toList.reverse.bind (fun (k, _) => [k])
  let ty1' := [: ∀ ⟨fvs.length⟩ => ⟨Ty.generalize fvs 0 ty1'⟩ :]
  let (i, x, env_tmx) := (i + 1, Tm.fvar i, PHashMap.from_list [(i, ty1')]) 
  let t := Tm.instantiate 0 [x] t 
  List.bind (infer i env_ty (env_tm ;; env_tmx) closed t ty) (fun (i, env_ty2, ty') =>
    [ (i, env_ty2, ty') ]
  ))

| .fix t1 =>
  List.bind (infer i (env_ty) env_tm True t1 (Ty.case ty ty)) (fun (i, env_ty1, ty1') =>
  let (i, ty_prem) := (i + 1, Ty.fvar i) 
  let (i, ty_conc) := (i + 1, Ty.fvar i) 
  List.bind (unify i (env_ty ;; env_ty1) True ty1' (.case ty_prem ty_conc)) (fun (i, env_ty2) =>
    let ty_prem := Ty.subst (env_ty ;; env_ty1 ;; env_ty2) ty_prem 
    let ty_conc := Ty.subst (env_ty ;; env_ty1 ;; env_ty2) ty_conc

    let fvs := (Ty.free_vars ty_prem).toList.bind (fun (k, _) => [k])

    let ty' := [: ν β[0] => 
      (∀ ⟨fvs.length⟩ :: 
        β[⟨fvs.length⟩] ≤ ⟨Ty.generalize fvs 0 ty_prem⟩ => 
        ⟨Ty.generalize fvs 0 ty_conc⟩ 
      )
    :]

    [ (i, env_ty1 ;; env_ty2, ty') ]
  ))

partial def infer_reduce_wt (t : Tm) (ty : Ty): Ty :=
  (infer 31 {} {} False t ty).foldl (fun acc => fun  (_, env_ty, ty) =>
    Ty.simplify (Ty.subst_default True (Ty.subst env_ty (Ty.union acc ty)))
  ) (Ty.bot)

partial def infer_reduce (t : Tm) : Ty := infer_reduce_wt t [: α[30] :]

-- testing below

#eval [: β[0] :]
#eval [: β[0] :]

#check [: β[0] | α[0] :]
#check [: β[0] ; α[0] :]
#check [: β[0] × α[0] :]
#check [: β[0] + α[0] :]
def x := 0
#check [: ∀ 1 :: β[0] ≤ α[0] => β[⟨x⟩] :]
#check [: ∀ 1 :: β[0] ≤ α[0] => β[0] :]
#check [: ∀ 2 :: α[0] ≤ α[0] => β[0] :]
#check [: ∀ 2 => β[0] :]
#check [: @ :]
#check [: α[24] :]
#check [: foo ^ @ :]
#check [: foo ^ @ | (boo ^ @) :]
#check [: μ β[0] => foo ^ @ :]
#check [: foo ^ boo ^ @ :]
#check [: μ β[0] => foo ^ boo ^ @ :]
#check [: μ β[0] => foo ^ β[0] :]
#check [: μ β[0] => foo ^ β[0]  ; α[0] | α[2] ; α[0]:]
#check [: β[3] ; α[0] -> α[1] | α[2] :]
#check [: μ β[0] => foo ^ β[0] ; α[0] | α[2] ; α[0] -> α[1] | α[2] :]
#check [: μ β[0] => foo ^ β[0] ; α[0] | α[2] ; α[0] :]
#check [: α[0] :]

#eval [: ∀ 2 :: α[0] ≤ α[0] => β[0] :]
#eval [: μ β[0] => foo ^ β[0] ; α[0] | α[2] ; α[0] :]


#eval ({} : PHashMap Nat Ty)

def zero_ := [: 
    zero ^ @
:]

#eval (unify 3 {} False [:
    (dumb^@)
:] zero_)

#eval unify 3 {} False [:
    (zero^@)
:] zero_

/-
  μ nat .
    zero^@ | 
    succ^nat 
-/
def nat_ := [: 
  μ β[0] => 
    zero^@ |
    succ^β[0]
:]
#eval nat_

def even := [: 
  μ β[0] => 
    zero^@ |
    succ^succ^β[0]
:]


def weven := [: 
  μ β[0] => 
    zero^@ |
    succ^dumb^β[0]
:]

#eval unify 3 {} True weven nat_ 
#eval unify 3 {} True even nat_ 
#eval unify 3 {} True nat_ even


#eval unify 3 {} True 
[: ∃ 2 :: β[0] ≤ ⟨even⟩ => β[0] × β[1]:] 
[: ∃ 2 :: β[0] ≤ ⟨nat_⟩ => β[0] × β[1]:] 

#eval unify 3 {} True 
[: ∃ 2 :: ⟨even⟩ ≤ β[0] => β[0] × β[1]:] 
[: ∃ 2 :: ⟨nat_⟩ ≤ β[0] => β[0] × β[1]:] 

#eval unify 3 {} False 
[: ∃ 2 :: β[0] ≤ ⟨nat_⟩ => β[0] × β[1]:] 
[: ∃ 2 :: β[0] ≤ ⟨even⟩ => β[0] × β[1]:] 

#eval unify 3 {} False 
[: ∃ 2 :: ⟨nat_⟩ ≤ β[0] => β[0] × β[1]:] 
[: ∃ 2 :: ⟨even⟩ ≤ β[0] => β[0] × β[1]:] 

#eval unify 3 {} False [:
    (zero^@)
:] nat_ 

#eval unify 3 {} False [:
    (succ^(zero^@))
:] nat_ 

#eval unify 3 {} False 
[: (succ^(α[0])) :] 
nat_ 

#eval unify_reduce 
[: (succ^(α[0])) :] 
nat_ 
[: α[0] :]

def nat_list := [: 
  μ β[0] => (
    (l ~ zero^@ ; r ~ nil^@) |
    (∃ 2 :: l ~ β[0] ; r ~ β[1] ≤ β[2] => 
      (l ~ succ^β[0] ; r ~ cons^β[1]))
  )
:]

def even_list := [: 
  μ β[0] => (
    (l ~ zero^@ ; r ~ nil^@) |
    (∃ 2 :: l ~ β[0] ; r ~ β[1] ≤ β[2] => 
      (l ~ succ^succ^β[0] ; r ~ cons^cons^β[1]))
  )
:]

-- TODO
#eval unify 3 {} False
  nat_list
  even_list

#eval unify 3 {} False
  even_list
  nat_list

#eval unify 3 {} True 
[: ∃ 1 :: β[0] ≤ ⟨even⟩ => hello ^ β[0] :]
[: ∃ 1 :: β[0] ≤ ⟨nat_⟩ => hello ^ β[0] :]

#eval unify 3 {} True 
[: ∃ 1 :: β[0] ≤ ⟨nat_⟩ => hello ^ β[0] :]
[: ∃ 1 :: β[0] ≤ ⟨even⟩ => hello ^ β[0] :]

#eval unify 3 {} False
  [: (l ~ zero^@ ; r ~ nil^@) :] 
  nat_list

#eval unify 3 {} False
  [: (l ~ zero^@ ; r ~ dumb^@) :] 
  nat_list

-- this is record type is not wellformed 
#eval unify 3 {} False
  [: (l ~ α[0] ; r ~ α[1]) :] 
  nat_list

-- this is record type is not wellformed 
#eval unify_reduce
  [: (l ~ α[0] ; r ~ α[1]) :] 
  nat_list
  [: ⊤ :]

#eval unify 3 {} False
  [: (l ~ zero^@ ; r ~ α[0]) :] 
  nat_list

-- expected α[0] → /nil
#eval unify 3 {} False
  [: (l ~ succ^zero^@ ; r ~ cons^α[0]) :] 
  nat_list

#eval unify 3 {} False
  [: (l ~ succ^succ^zero^@ ; r ~ cons^α[0]) :] 
  nat_list


def examp1 := unify 3 {} False
  [: (l ~ succ^succ^zero^@ ; r ~ cons^α[0]) :] 
  nat_list

#eval unify_reduce 
  [: (l ~ succ^succ^zero^@ ; r ~ cons^α[0]) :] 
  nat_list
  [: α[0]:]


#eval unify 3 {} False
  [: (l ~ succ^zero^@ ; r ~ cons^cons^α[0]) :] 
  nat_list



def nat_to_list := [: 
  ν β[0] => 
    (zero^@ -> nil^@) ; 
    (∀ 2 :: β[2] ≤ β[0] -> β[1] => 
      succ^β[0] -> cons^β[1])
:]

#eval unify 3 {} False 
  nat_to_list
  [: (succ^zero^@) -> (cons^nil^@) :] 

#eval unify_reduce 
  nat_to_list
  [: (succ^zero^@) -> (cons^nil^@) :] 
  [: ⊤ :]

#eval unify_reduce
  nat_to_list
  [: (succ^zero^@ -> cons^α[0]) :] 
  [: α[0] :]

#eval unify_reduce
  nat_to_list
  [: (succ^zero^@ -> cons^cons^α[0]) :] 
  [: α[0] :]


/-
  μ plus .
    ∃ N .  
      zero^@ × N × N | 

    ∃ X Y Z :: X, Y, Z ≤ plus .  
      succ^X × Y × succ^Z
-/
def plus := [: 
  μ β[0] => 
    (∃ 1 => 
      (x ~ zero^@ ; y ~ β[0] ; z ~ β[0])) |

    (∃ 3 :: (x ~ β[0] ; y ~ β[1] ; z ~ β[2]) ≤ β[3] => 
      (x ~ succ^β[0] ; y ~ β[1] ; z ~ succ^β[2]))
:]

-- /print plus

-- #eval [: (x ~ zero^@ ; y ~ zero^@ ; z ~ zero^@) :]  
-- #eval [: succ^succ^zero^@ :]  


#eval unify_reduce [:
    x ~ zero^@ ;
    y ~ α[0] ;
    z ~ zero^@
:] plus [: α[0] :]


#eval unify_reduce [:
  (
    x ~ (succ^zero^@) ;
    y ~ (succ^zero^@) ;
    z ~ (α[0])
  )
:] plus [: α[0] :]


#eval unify_reduce [:
  (
    x ~ (succ^succ^zero^@) ;
    y ~ (succ^zero^@) ;
    z ~ (α[0])
  )
:] plus
[: α[0] :]

#eval unify_reduce [:
  (
    x ~ (succ^zero^@) ;
    y ~ (α[0]) ;
    z ~ (succ^succ^zero^@)
  )
:] plus
[: α[0] :]

#eval unify_reduce [:
  (
    x ~ (succ^zero^@) ;
    y ~ (succ^succ^zero^@) ;
    z ~ (α[0])
  )
:] plus [: α[0] :]


-- expected: α[0] ↦ succ^zero^@
#eval unify_reduce [:
(
  x ~ α[0] ;
  y ~ succ^zero^@ ;
  z ~ succ^succ^zero^@
)
:] plus
[: α[0] :]


#eval unify_reduce [:
(
  x ~ succ^zero^@ ;
  y ~ α[0] ;
  z ~ succ^succ^zero^@
)
:] plus
[: α[0] :]


#eval unify_reduce [:
(
  x ~ (α[0]) ;
  y ~ (α[1]) ;
  z ~ (succ^succ^zero^@)
)
:] plus
[: x ~ α[0] ; y ~ α[1] :]

#eval unify_reduce [:
(
  x ~ (succ^succ^zero^@) ;
  y ~ (α[1]) ;
  z ~ (α[0])
)
:] plus
[: y ~ α[1] ; z ~ α[0] :]


-- term testing
#eval [:
  λ[ 
    for y[0] : α[0] => y[0],
    for y[0] : α[0] => y[0] 
  ]
:]

#eval [:
  ω[ 
    left := x[0],
    right := x[0]
  ]
:]


#eval [:
  succ#zero#()
:]



#eval infer_reduce [:
  succ#zero#()
:]

#eval [:
  succ#zero#()
:]

#eval [:
  x[0]/hello
:]

#eval infer_reduce [:
  _ 
:]


#eval [:
  α[0] + α[1]
:]

#eval [:
  α[0] × α[1]
:]

#eval [:
  (x[0], x[1])
:]


#eval infer_reduce [:
  λ [for y[0] => y[0]]
:]

#eval infer_reduce [:
  λ [for y[0] : abc^@ => y[0]]
:]

#eval infer_reduce [:
  λ [for y[0] : inp^@ -> out^@ =>
  Out # λ [for y[0] => 
      cons # ((y[1] y[0]), nil # ())
  ]
  ]
:]

#eval infer_reduce [:
  ((), nil # ())
:]

  
#eval [:
  hello^thing~@
  
:]

#eval infer_reduce [:
  λ y[0] : nat^@ =>
    let y[0] = (λ (y[0], y[1]) : (str^@ × str^@) => y[0]) =>
    (y[0] (str#(), str#()))
:]

#eval infer_reduce [:
  λ y[0] : nat^@ =>
    let y[0] = (λ (y[0], y[1]) : (str^@ × str^@) => y[0]) =>
    (y[0] (_, str#()))
:]

#eval infer_reduce [:
  λ y[0] : nat^@ =>
    let y[0] = λ[for (y[0], y[1]) : (str^@ × str^@) => y[0]] =>
    (y[0] (y[1], _))
:]

-- Propagation: Down 
-- even though, there is a hole in the program,
-- the type of α[0] can be inferred to be uno^@  
-- due to the application and downward propagation
#eval infer_reduce [:
  λ y[0] : α[0] =>
    let y[0] = (λ (y[0], y[1]) : (uno^@ × dos^@) => y[1]) =>
    (y[0] (y[1], _))
:]

-- Propagation: Up
#eval infer_reduce [:
  λ y[0] : hello^@ -> world^@ =>
  λ y[0] => 
    (cons # ((y[1] y[0]), nil # ()))
:]

#eval infer_reduce [:
  λ y[0] : int^@ -> str^@ => 
  λ y[0] : int^@  =>
    (y[1] y[0])
:]


#eval infer_reduce [:
  λ y[0] : str^@ -> @ => 
  λ y[0] : str^@ => 
     (OUTPUT # (y[1] y[0]))
:]

#eval infer_reduce [:
  λ y[0] : int^@ -> @ => 
  λ y[0] : str^@ => 
     (y[1] y[0]) 
:]

#eval infer_reduce [:
  λ y[0] : (int^@ | str^@) -> @ => 
  λ y[0] : str^@ => 
     (y[1] y[0]) 
:]

#eval infer_reduce [:
  λ y[0] : (int^@ | α[1]) -> α[1] => 
  λ y[0] : str^@ => 
     (y[1] y[0]) 
:]

#eval infer_reduce [:
  λ y[0] : ∀ 1 => (β[0] -> β[0]) => 
  λ y[0] : int^@  =>
    (y[1] y[0])
:]



-----

-- Widening
#eval infer_reduce [:
  λ y[0] : α[1] -> (α[1] -> (α[1] × α[1])) => 
    (OUTPUT # (y[0] hello#()))
:]

-- Widening
#eval infer_reduce [:
  λ y[0] : α[1] -> (α[1] -> (α[1] × α[1])) => 
    (OUTPUT # ((y[0] hello#()) world#()))
:]


-- Widening
#eval infer_reduce [:
  λ y[0] : α[1] -> (α[1] -> (α[1] × α[1])) => 
  λ y[0] : hello^@ =>
  λ y[0] : world^@ =>
    OUTPUT # ((y[2] y[1]) y[0])
:]

-- Widening
#eval infer_reduce [:
  λ y[0] : ∀ 1 => β[0] -> β[0] -> (β[0] × β[0]) => 
  λ y[0] : hello^@ =>
  λ y[0] : world^@ =>
    OUTPUT # ((y[2] y[1]) y[0])
:]

#eval infer_reduce [:
  λ y[0] : α[1] -> (α[1] -> (α[1] × α[1])) => 
  let y[0] = ((y[0] hello#()) world#()) =>
    OUTPUT # y[0]
:]


#eval infer_reduce [:
  λ y[0] : ∀ 1 => β[0] -> β[0] -> (β[0] × β[0]) => 
  λ y[0] : int^@  =>
  λ y[0] : str^@  =>
  let y[0] = ((y[2] y[1]) y[0]) =>
  OUTPUT # y[0]
:]

#eval infer_reduce [:
  let y[0] = (hello # ()) =>
  y[0]
:]

-- Narrowing

#eval [:
  λ y[0] : uno^@ -> @ => y[0]
:]
#eval [:
  λ y[0] : uno^@ -> @ => 
  λ y[0] : dos^@ -> @ =>
  λ y[0] =>
    ((y[2] y[0]), (y[1] y[0]))
:]
#eval infer_reduce [:
  λ y[0] : uno^@ -> @ => 
  λ y[0] : dos^@ -> @ =>
  OUTPUT # (
    λ y[0] => ((y[2] y[0]), (y[1] y[0]))
  )
:]
#eval infer_reduce [:
  λ y[0] : uno^@ -> @ => 
  λ y[0] : dos^@ -> @ =>
  OUTPUT # (λ y[0] =>
    ((y[2] y[0]), (y[1] y[0]))
  )
:]


-- let-polymorphism

#eval infer_reduce [:
  let y[0] = (λ y[0] : str^@ => hello # y[0]) =>
  (y[0] str#())
:]

#eval infer_reduce [:
  let y[0] = (λ y[0] => hello # y[0]) =>
  (
    y[0]
  )
:]

#eval infer_reduce [:
  let y[0] = (λ y[0] => hello # y[0]) =>
  (y[0] uno#())
:]


#eval infer_reduce [:
  let y[0] = (λ y[0] => hello # y[0]) =>
  (
    (y[0] uno#()),
    (y[0] dos#())
  )
:]




def repli := [:
  ∀ 1 => β[0] -> (ν β[0] =>
    (zero^@ -> nil^@) ;
    (∀ 2 :: β[2] ≤ (β[0] -> β[1]) =>
      succ^β[0] -> cons^(β[3] × β[1])
    )
  )
:]


-----

#eval unify 3 {} True 
[: uno ~ @ ; dos ~ @ ; tres ~ @:]
[: uno ~ @ ; tres ~ @:]

#eval unify 3 {} True 
[: uno ~ @ ; dos ~ @ ; tres ~ @:]
[: ∀ 1 :: β[0] ≤ uno ~ @ | dos ~ @ | tres ~ @ => β[0]:]

#eval unify 3 {} True 
[: ∀ 1 :: β[0] ≤ uno ~ @ | dos ~ @ | tres ~ @ => β[0]:]
[: uno ~ @ ; dos ~ @ ; tres ~ @:]


#eval unify 3 {} True 
[: uno ~ @ | dos ~ @ | tres ~ @ :]
[:dos ~ @ ; tres ~ @ :]

#eval unify 3 {} True 
[:dos ~ @ ; tres ~ @ ; four ~ @:]
[: uno ~ @ | dos ~ @ | tres ~ @ :]

#eval unify 3 {} True 
[: ∀ 1 :: β[0] ≤ uno ~ @ | dos ~ @ | tres ~ @ => β[0]:]
[:dos ~ @ ; tres ~ @ ; four ~ @:]

#eval unify 3 {} True 
[: ∀ 1 :: uno ~ @ ; dos ~ @ ; tres ~ @ ≤ β[0] => β[0]:]
[:dos ~ @ ; tres ~ @ :]

#eval unify 3 {} True 
[: ∀ 1 :: uno ~ @ ; dos ~ @ ; tres ~ @ ≤ β[0] => β[0]:]
[: ∀ 1 :: uno ~ @ ; dos ~ @ ≤ β[0] => β[0]:]

#eval unify 3 {} True 
[: ∀ 1 :: uno ~ @ ; dos ~ @ ≤ β[0] => β[0]:]
[: ∀ 1 :: uno ~ @ ; dos ~ @ ; tres ~ @ ≤ β[0] => β[0]:]

#eval unify 3 {} True 
[: ∀ 1 :: β[0] ≤ ⟨even⟩ => hello ^ β[0] :]
[: ∀ 1 :: β[0] ≤ ⟨nat_⟩ => hello ^ β[0] :]

#eval unify 3 {} True 
[: ∀ 1 :: β[0] ≤ ⟨nat_⟩ => hello ^ β[0] :]
[: ∀ 1 :: β[0] ≤ ⟨even⟩ => hello ^ β[0] :]

#eval unify 3 {} True 
[: ∀ 1 :: uno ~ @ ; dos ~ @ ; tres ~ @ ≤ β[0] => β[0]:]
[: ∀ 1 :: uno ~ @ ; dos ~ @ ; four ~ @ ≤ β[0] => β[0]:]

#eval unify 3 {} True 
[: ∀ 1 :: β[0] ≤ uno ~ @ => β[0]:]
[:uno ~ @ ; four ~ @:]

#eval unify 3 {} True 
[: ∀ 1 :: uno ~ @ ≤ β[0] => β[0]:]
[:uno ~ @ ; four ~ @:]


----- 

def nat_to_unit := [: 
  ν β[0] => 
    (zero^@ -> @) ; 
    (∀ 1 :: β[1] ≤ β[0] -> @ => 
      (succ^β[0]) -> @) 
:]

def even_to_unit := [: 
  ν β[0] => 
    (zero^@ -> @) ; 
    (∀ 1 :: β[1] ≤ β[0] -> @ => 
      (succ^succ^β[0]) -> @)
:]

#eval unify 3 {} False 
nat_to_unit
[: (zero^@ -> @) :]

#eval unify 3 {} True 
nat_to_unit
nat_to_unit

#eval unify 3 {} True 
nat_to_unit
[: (succ^zero^@ -> @) :]

#eval unify 3 {} True 
even_to_unit
[: (succ^succ^zero^@ -> @) :]

#eval unify 3 {} True 
even_to_unit
[: (succ^zero^@ -> @) :]

-- #eval unify 3 {} True 
-- [: 
--     (zero^@ -> @) ; 
--     (∀ 1 :: ⟨nat_to_unit⟩ ≤ β[0] -> @ => 
--       (succ^β[0]) -> @) 
-- :]
-- [: 
--     (zero^@ -> @) ; 
--     (∀ 1 :: ⟨nat_to_unit⟩ ≤ β[0] -> @ => 
--       (succ^succ^β[0]) -> @)
-- :]

-- #eval unify 3 {} True 
-- nat_to_unit
-- even_to_unit

-- #eval unify 3 {} True 
-- even_to_unit
-- nat_to_unit

-- #eval unify 3 {} True 
-- nat_
-- even


#eval repli

#eval [:
  λ y[0] => fix (λ y[0] => λ[
  for zero#() => nil#(),
  for succ#y[0] => cons#(y[2], (y[1] y[0])) 
  ]) 
:]

#eval infer_reduce [:
  λ[
  for zero#() => nil#(),
  for succ#y[0] => cons#((), ()) 
  ] 
:]


#eval [: (zero^@ -> nil^@) ; (succ^⊤ -> cons^(@ × ⊥)) :]

#eval unify_reduce
[: α[2] -> ((zero^@ -> nil^@) ; (succ^⊤ -> cons^(@ × @))) :]
[: α[0] -> α[0] :]
[: α[0] :]

#eval infer_reduce_wt 
[:
  (λ y[0] => λ[
  for zero#() => nil#(),
  for succ#y[0] => cons#((), (y[1] y[0])) 
  ]) 
:]
[: α[20] -> α[20] :]


#eval [:
  ∀ 1 => β[0] -> (ν β[0] =>
    (zero^@ -> nil^@) ;
    (∀ 2 :: β[2] ≤ (β[0] -> β[1]) =>
      succ^β[0] -> cons^(β[3] × β[1])
    )
  )
:]

#eval unify_reduce
[: (α[0] -> α[1]) -> ((zero^@ -> nil^@) ; (succ^α[0] -> cons^(@ × α[1]))) :]
[: α[20] -> α[20] :]
[: α[20] :]


#eval infer_reduce [:
  fix (λ y[0] => λ[
  for zero#() => nil#(),
  for succ#y[0] => cons#((), (y[1] y[0])) 
  ]) 
:]