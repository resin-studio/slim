import Std.Data.BinomialHeap
import Init.Data.Hashable
import Lean.Data.PersistentHashMap
-- import Mathlib.Data.List.Sort

-- Sorting
-- copied from MathLib; import not working
section sorting
def split : List α → List α × List α
  | [] => ([], [])
  | a :: l =>
    let (l₁, l₂) := split l
    (a :: l₂, l₁)

partial def merge (r : α -> α -> Bool) : List α → List α → List α
  | [], l' => l'
  | l, [] => l
  | a :: l, b :: l' =>
    if r a b then a :: merge r l (b :: l') else b :: merge r (a :: l) l'

partial def mergeSort (r : α -> α -> Bool): List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: l => 
    let ls := (split (a :: b :: l))
    merge r (mergeSort r ls.1) (mergeSort r ls.2)

end sorting

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

infixl:65   " ; " => PHashMap.insert_all

def PHashMap.from_list [BEq α] [Hashable α] 
(source : List (α × β)) : PHashMap α β :=
  source.foldl (init := {}) fun m (k, v) => m.insert k v

protected def PHashMap.repr [Repr (α × β)] [BEq α] [Hashable α] 
(m : PHashMap α β) (n : Nat) : Format :=
  List.repr (toList m) n

instance [Repr (α × β)] [BEq α] [Hashable α] : Repr (PHashMap α β) where
  reprPrec := PHashMap.repr


-- TODO: convert top and bottom into sugar: ⊤ = ∃ α . α, ⊥  = ∀ α . α
-- TODO: remove top and bottom types 
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
  (l ++ "*" ++ (Ty.repr ty1 n))
| .field l ty1 => 
  (l ++ " ~ " ++ (Ty.repr ty1 n))

| .union (Ty.tag "inl" inl) (Ty.tag "inr" inr) =>
  Format.bracket "(" ((Ty.repr inl n) ++ " +" ++ Format.line ++ (Ty.repr inr n)) ")"
| .union ty1 ty2 =>
  let _ : ToFormat Ty := ⟨fun ty' => Ty.repr ty' n ⟩
  let tys := [ty1, ty2] 
  Format.bracket "("
    (Format.joinSep tys (" ∨" ++ Format.line))
  ")"

| .inter (Ty.field "l" l) (Ty.field "r" r) =>
  Format.bracket "(" ((Ty.repr l n) ++ " × " ++ (Ty.repr r n)) ")"
| .inter ty1 ty2 =>
  Format.bracket "(" ((Ty.repr ty1 n) ++ " ∧ " ++ (Ty.repr ty2 n)) ")"
| .case ty1 ty2 =>
  Format.bracket "(" ((Ty.repr ty1 n) ++ " ->" ++ Format.line ++ (Ty.repr ty2 n)) ")"
| .univ n ty_c1 ty_c2 ty_pl =>
  if (ty_c1, ty_c2) == (Ty.unit, Ty.unit) then
    Format.bracket "(" (
      "∀ " ++ (repr n) ++ " =>" ++ Format.line ++ 
      (Ty.repr ty_pl n)
    ) ")"
  else
    Format.bracket "(" (
      "∀ " ++ (repr n) ++ " :: " ++
      (Ty.repr ty_c1 n) ++ " ≤ " ++ (Ty.repr ty_c2 n) ++ " =>" ++ Format.line ++ 
      (Ty.repr ty_pl n)
    ) ")"
| .exis n ty_c1 ty_c2 ty_pl =>
  if (ty_c1, ty_c2) == (Ty.unit, Ty.unit) then
    Format.bracket "(" (
      "∃ " ++ (repr n) ++ " =>" ++ Format.line ++ 
      (Ty.repr ty_pl n)
    ) ")"
  else
    Format.bracket "(" (
      "∃ " ++ (repr n) ++ " :: " ++
      (Ty.repr ty_c1 n) ++ " ≤ " ++ (Ty.repr ty_c2 n) ++ " =>" ++ Format.line ++ 
      (Ty.repr ty_pl n)
    ) ")"
| .recur ty1 =>
  Format.bracket "(" (
    "μ β[0] => " ++ (Ty.repr ty1 n)
  ) ")"
| .corec ty1 =>
  Format.bracket "(" (
    "ν β[0] => " ++ (Ty.repr ty1 n)
  ) ")"

instance : Repr Ty where
  reprPrec := Ty.repr


inductive Tm : Type
| hole : Tm 
| unit : Tm
| bvar : Nat -> Tm 
| fvar : Nat -> Tm 
| tag : String -> Tm -> Tm
| record : List (String × Tm) -> Tm
| func : List (Tm × Tm) -> Tm
| proj : Tm -> String -> Tm
| app : Tm -> Tm -> Tm
| letb : Ty -> Tm -> Tm -> Tm
| fix : Tm -> Tm
deriving Repr, Inhabited, BEq

def indent(n : Nat) : String :=
  Nat.fold (fun | _, acc => acc ++ "  " ) n ""


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
syntax:90 slm:100 "*" slm:90 : slm
syntax:90 slm:100 "~" slm:90 : slm
syntax:50 slm:51 "->" slm:50 : slm
syntax:60 slm:61 "∨" slm:60 : slm
syntax:60 slm:61 "+" slm:60 : slm
syntax:70 slm:71 "∧" slm:70 : slm
syntax:70 slm:71 "×" slm:70 : slm
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
syntax:30 slm:100 ";" slm:30 : slm
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
| `([: $a * $b:slm :]) => `(Ty.tag [: $a :] [: $b :])
| `([: $a ~ $b:slm :]) => `(Ty.field [: $a :] [: $b :])
| `([: $a -> $b :]) => `(Ty.case [: $a :] [: $b :])
| `([: $a ∨ $b :]) => `(Ty.union [: $a :] [: $b :])
| `([: $a + $b :]) => `(Ty.union (Ty.tag "inl" [: $a :]) (Ty.tag "inr" [: $b :]))
| `([: $a ∧ $b :]) => `(Ty.inter [: $a :] [: $b :])
| `([: $a × $b :]) => `(Ty.inter (Ty.field "l" [: $a :]) (Ty.field "r" [: $b :]))
| `([: ∀ $a :: $b ≤ $c => $d :]) => `(Ty.univ [: $a :] [: $b :] [: $c :] [: $d :])
| `([: ∀ $a:slm => $b:slm :]) => `(Ty.univ [: $a :] [: @ :] [: @ :] [: $b :] )
| `([: ∃ $a :: $b ≤ $c => $d  :]) => `(Ty.exis [: $a :] [: $b :] [: $c :] [: $d :])
| `([: ∃ $a:slm => $b:slm :]) => `(Ty.exis [: $a :] [: @ :] [: @ :] [: $b :] )
| `([: μ β[0] => $a :]) => `(Ty.recur [: $a :])
| `([: ν β[0] => $a :]) => `(Ty.corec [: $a :])
--Tm
| `([: _ :]) => `(Tm.hole)
| `([: () :]) => `(Tm.unit)
| `([: y[$n] :]) => `(Tm.bvar [: $n :])
| `([: x[$n] :]) => `(Tm.fvar [: $n :])
| `([: $a ; $b :]) => `(Tm.tag [: $a :] [: $b :])
| `([: $a := $b :]) => `(([: $a :], [: $b :]))
| `([: for $b => $d :]) => `(([: $b :], [: $d :]))
| `([: ω $a :]) => `(Tm.record [: $a :])
| `([: ( $a , $b ) :]) => `(Tm.record [("l", [: $a :]), ("r", [:$b :])])
| `([: λ $b => $d :]) => `(Tm.func [([: $b :], [: $d :])])
| `([: λ $a :]) => `(Tm.func [: $a :])
| `([: $a / $b :]) => `(Tm.proj [: $a :] [: $b :])
| `([: ($a $b) :]) => `(Tm.app [: $a :] [: $b :])
| `([: let y[0] : $a = $b => $c :]) => `(Tm.letb [: $a :] [: $b :] [: $c :])
| `([: let y[0] = $b => $c :]) => `(Tm.letb [: ∃ 1 => β[0] :] [: $b :] [: $c :])
| `([: fix $a :]) => `(Tm.fix [: $a :])

-- generic
  | `([: ($a) :]) => `([: $a :])

--escape 
  | `([: ⟨ $e ⟩ :]) => pure e


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
  l ++ ";" ++ (Tm.repr t1 n)
| record [("l", l), ("r", r)] =>
  let _ : ToFormat Tm := ⟨fun t1 => Tm.repr t1 n ⟩
  Format.bracket "(" (Format.joinSep [l, r] ("," ++ Format.line)) ")"
| record fds =>
  let _ : ToFormat (String × Tm) := ⟨fun (l, t1) =>
    l ++ " := " ++ Tm.repr t1 n ⟩
  "ω" ++ Format.bracket "[" (Format.joinSep fds ("," ++ Format.line)) "]"
| func [(pat, tb)] =>
  "λ " ++ (Tm.repr pat n) ++ " => " ++ (Tm.repr tb (n))
| func fs =>
  let _ : ToFormat (Tm × Tm) := ⟨fun (pat, tb) =>
    "for " ++ (Tm.repr pat n) ++ " => " ++ (Tm.repr tb (n))
  ⟩
  "λ" ++ Format.bracket "[" (Format.joinSep fs ("," ++ Format.line)) "]"
| .proj t1 l =>
  Tm.repr t1 n ++ "/" ++ l
| .app t1 t2 =>
  Format.bracket "(" (Tm.repr t1 n) ") " ++ "(" ++ Tm.repr t2 n ++ ")"
| .letb ty1 t1 t2 =>
  match ty1 with
  | .univ 1 Ty.bot Ty.top (Ty.bvar 0) =>
    "let y[0] : " ++ (Ty.repr ty1 n) ++ " = " ++  (Tm.repr t1 n) ++ " =>" ++
    Format.line  ++ (Tm.repr t2 n) 
  | _ =>
    "let y[0] = " ++  (Tm.repr t1 n) ++ " =>" ++
    Format.line  ++ (Tm.repr t2 n) 
| .fix t1 =>
  Format.bracket "(" ("fix " ++ (Tm.repr t1 n)) ")"

instance : Repr Tm where
  reprPrec := Tm.repr



def lookup (key : Nat) : List (Nat × T) -> Option T
| (k,v) :: bs => if key = k then some v else lookup key bs 
| [] => none


def lookup_record (key : String) : List (String × T) -> Option T
| (k,v) :: bs => if key = k then some v else lookup_record key bs 
| [] => none


partial def Ty.subst (m : PHashMap Ty Ty) : Ty -> Ty
| .bvar id => .bvar id 
| .fvar id => (match m.find? (.fvar id) with
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


-- assume assoc right
def Ty.inter_contains : Ty -> Ty -> Bool 
| ty1, Ty.inter ty21 ty22 => 
  Ty.inter_contains ty1 ty21 ||
  Ty.inter_contains ty1 ty22
| ty1, ty2 => ty1 == ty2

-- make assoc right
def Ty.intersect : Ty -> Ty -> Ty
| Ty.bot, ty2 => Ty.bot 
| Ty.top, ty2 => ty2
| Ty.inter ty11 ty12, ty2 => Ty.intersect ty11 (Ty.intersect ty12 ty2) 
| ty1, Ty.bot => Ty.bot 
| ty1, Ty.top => ty1
| ty1, ty2 => 
    if Ty.inter_contains ty1 ty2 then
      ty2
    else
      Ty.inter ty1 ty2


-- assume assoc right
def Ty.union_contains : Ty -> Ty -> Bool 
| ty1, Ty.union ty21 ty22 => 
  Ty.union_contains ty1 ty21 ||
  Ty.union_contains ty1 ty22
| ty1, ty2 => ty1 == ty2

-- make assoc right
def Ty.unionize : Ty -> Ty -> Ty
| Ty.top, ty2 => Ty.top
| Ty.bot, ty2 => ty2
| Ty.union ty11 ty12, ty2 => Ty.unionize ty11 (Ty.unionize ty12 ty2) 
| ty1, Ty.top => Ty.top
| ty1, Ty.bot => ty1
| ty1, ty2 => 
    if Ty.union_contains ty1 ty2 then
      ty2
    else
      Ty.union ty1 ty2

partial def Ty.simplify : Ty -> Ty
| .bvar id => Ty.bvar id  
| .fvar id => Ty.fvar id 
| .unit => .unit 
| .bot => .bot 
| .top => .top 
| .tag l ty => Ty.tag l (Ty.simplify ty) 
| .field l ty => Ty.field l (Ty.simplify ty) 
| .union ty1 ty2 => Ty.unionize (Ty.simplify ty1) (Ty.simplify ty2)
| .inter ty1 ty2 => Ty.intersect (Ty.simplify ty1) (Ty.simplify ty2)
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


def Ty.reduce (env_ty : PHashMap Ty Ty) (ty : Ty) :=
  (Ty.simplify (Ty.subst (env_ty) ty))



declare_syntax_cat sub
syntax slm "//" slm : sub 
syntax "[" sub,+ "]" : sub
syntax "[sub:" sub ":]" : term 

macro_rules
  | `([sub: $a:slm // $b:slm :]) => `(([: $a :], [: $b :])) 

macro_rules
  | `([sub: [$x:sub] :]) => `([ [sub: $x :] ])
  | `([sub: [$x,$xs:sub,*] :]) => `([sub: $x :] :: [sub: [$xs,*] :])


-- syntax slm ";" sub : slm 
-- macro_rules
--   | `([: $a ; $b:sub :]) => `(Ty.subst (PHashMap.from_list [sub: $b :]) [: $a :])


-- #check [: (β[1]) ; [1 // α[0]] :]
-- #check [: (β[1]) ; [1//α[0]] :]



partial def Ty.free_vars: Ty -> PHashMap Nat Unit
| .bvar id => {} 
| .fvar id => PHashMap.from_list [(id, Unit.unit)] 
| .unit => {} 
| .bot => {} 
| .top => {} 
| .tag l ty => (Ty.free_vars ty) 
| .field l ty => (Ty.free_vars ty)
| .union ty1 ty2 => Ty.free_vars ty1 ; Ty.free_vars ty2
| .inter ty1 ty2 => Ty.free_vars ty1 ; Ty.free_vars ty2
| .case ty1 ty2 => Ty.free_vars ty1 ; Ty.free_vars ty2
| .univ n ty_c1 ty_c2 ty => 
  (Ty.free_vars ty_c1);(Ty.free_vars ty_c2);(Ty.free_vars ty)
| .exis n ty_c1 ty_c2 ty =>
  (Ty.free_vars ty_c1);(Ty.free_vars ty_c2);(Ty.free_vars ty)
| .recur ty => (Ty.free_vars ty)
| .corec ty => (Ty.free_vars ty)


def Ty.signed_free_vars (posi : Bool) : Ty -> PHashMap Nat Unit
| .bvar id => {} 
| .fvar id => 
  if posi then
    let u : Unit := Unit.unit
    PHashMap.from_list [(id, u)] 
  else
    {}
| .unit => {} 
| .bot => {} 
| .top => {} 
| .tag l ty => (Ty.signed_free_vars posi ty) 
| .field l ty => (Ty.signed_free_vars posi ty)
| .union ty1 ty2 => Ty.signed_free_vars posi ty1 ; Ty.signed_free_vars posi ty2
| .inter ty1 ty2 => Ty.signed_free_vars posi ty1 ; Ty.signed_free_vars posi ty2
| .case ty1 ty2 => (Ty.signed_free_vars (!posi) ty1) ; Ty.signed_free_vars posi ty2
| .univ n ty_c1 ty_c2 ty => 
  (Ty.signed_free_vars posi ty)
| .exis n ty_c1 ty_c2 ty =>
  (Ty.signed_free_vars posi ty)
| .recur ty => (Ty.signed_free_vars posi ty)
| .corec ty => (Ty.signed_free_vars posi ty)


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


partial def roll_recur (key : Nat) (m : PHashMap Ty Ty) (ty : Ty) : Ty :=
  let ty := Ty.reduce m ty  
  if (Ty.free_vars ty).contains key then
    Ty.subst (PHashMap.from_list [(.fvar key, [: β[0] :])]) [: (μ β[0] => ⟨ty⟩) :] 
  else
    ty 

partial def roll_corec (key : Nat) (m : PHashMap Ty Ty) (ty : Ty) : Ty :=
  let ty := Ty.reduce m ty
  if (Ty.free_vars ty).contains key then
    Ty.subst (PHashMap.from_list [(.fvar key, [: β[0] :])]) [: (ν β[0] => ⟨ty⟩) :] 
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
      (Ty.subst_default true cty1) (Ty.subst_default false cty2)
      (Ty.subst_default sign ty)
| .exis n cty1 cty2 ty => 
    Ty.exis n  
      (Ty.subst_default true cty1) (Ty.subst_default false cty2)
      (Ty.subst_default sign ty)
| .recur ty => Ty.recur (Ty.subst_default sign ty)
| .corec ty => Ty.corec (Ty.subst_default sign ty)


partial def Ty.equal (env_ty : PHashMap Ty Ty) (ty1 : Ty) (ty2 : Ty) : Bool :=
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
| .top => some [] 
| _ => none



def wellformed_record_type (env_ty : PHashMap Ty Ty) (ty : Ty) : Bool :=
  match linearize_fields (Ty.simplify (Ty.subst env_ty ty)) with
  | .some fields => 
    List.any fields (fun (k_fd, ty_fd) =>
      match ty_fd with
      | .fvar _ => false 
      | _ => true 
    ) 
  | .none => false

partial def wellformed_unroll_type (env_ty : PHashMap Ty Ty) (ty : Ty) : Bool :=
  match (Ty.simplify (Ty.subst env_ty ty)) with 
  | .fvar _ => false
  | ty => (linearize_fields ty == .none) || (wellformed_record_type env_ty ty)


def extract_premise (start : Nat) : Ty -> Option Ty 
| .univ n (.bvar id) (Ty.case ty1 _) ty3 => 
  if id == start + n then
    Option.bind (extract_premise (start + n) ty3) (fun ty3_prem =>
    (Ty.exis n ty1 (.bvar (start + n)) ty3_prem)
    )
  else 
    none
| Ty.inter ty1 Ty.top => 
  (extract_premise start ty1)
| Ty.inter Ty.top ty2 => 
  (extract_premise start ty2)
| Ty.inter ty1 ty2 => 
  Option.bind (extract_premise start ty1) (fun ty1_prem =>
  Option.bind (extract_premise start ty2) (fun ty2_prem =>
    Ty.union ty1_prem ty2_prem
  ))
| Ty.case ty1 _ => some ty1 
| _ => none

def extract_relation (start : Nat) : Ty -> Option Ty 
| .univ n (.bvar id) (Ty.case ty1 ty2) ty3 => 
  if id == start + n then
    Option.bind (extract_relation (start + n) ty3) (fun ty3_rel =>
    (Ty.exis n [: ⟨ty1⟩ × ⟨ty2⟩ :] (.bvar (start + n)) ty3_rel)
    )
  else 
    none
| Ty.inter ty1 Ty.top => 
  (extract_relation start ty1)
| Ty.inter Ty.top ty2 => 
  (extract_relation start ty2)
| Ty.inter ty1 ty2 => 
  Option.bind (extract_relation start ty1) (fun ty1_rel =>
  Option.bind (extract_relation start ty2) (fun ty2_rel =>
    Ty.union ty1_rel ty2_rel
  ))
| Ty.case ty1 ty2 => some [: ⟨ty1⟩ × ⟨ty2⟩ :] 
| _ => none

def rewrite_function_type : Ty -> Option Ty 
| Ty.corec ty =>
  bind (extract_premise 0 ty) (fun prem =>
  bind (extract_relation 0 ty) (fun rel =>
    [:
      ∀ 1 :: β[0] ≤ ⟨Ty.recur prem⟩ => (
        β[0] -> (∃ 1 :: β[1] × β[0] ≤ ⟨Ty.recur rel⟩ => β[0])
      )
    :]
  )) 
| _ => none


partial def extract_record_labels : Ty -> PHashMap String Unit
| .field l ty => 
  let u := Unit.unit 
  PHashMap.from_list [(l, u)]
| .union ty1 ty2 => 
  (extract_record_labels ty1);(extract_record_labels ty2)
| .inter ty1 ty2 => 
  match linearize_fields (Ty.inter ty1 ty2) with
  | .none => {} 
  | .some fields => PHashMap.from_list (fields.map (fun (l, _) => (l, Unit.unit)))
| .exis n ty_c1 ty_c2 ty => (extract_record_labels ty)
| .recur ty => extract_record_labels ty
| _ => {} 

def intersect_fields : List (String × Ty) -> Ty
| [] => Ty.top 
| (l, ty) :: fields => Ty.inter (Ty.field l ty) (intersect_fields fields)

def normalize_fields (fields : List (String × Ty)) : Ty :=
  let fields_sorted := mergeSort (fun (l1, _) (l2, _) => l1 < l2) fields
  intersect_fields fields_sorted


-- α[0] ↦ ∃ β[0] :: β[0] × α[1] ≤ ⟨nat_list⟩ => β[0]   
-- succ * α[2] ≤ ∃ β[0] :: β[0] × α[1] ≤ ⟨nat_list⟩ => β[0]   
def separate_fields (prev_fields var_fields : List (String × Ty)) (ty_rhs : Ty) : PHashMap Nat Ty :=
match var_fields with
| [] => {}
| (l, ty_fd) :: var_fields' =>
  match ty_fd with
  | Ty.fvar id =>
    let fields := 
      prev_fields ++ (l, [: β[0] :]) :: var_fields 
    let ty_lhs := intersect_fields fields
    let ty := [: ∃ 1 :: ⟨ty_lhs⟩ ≤ ⟨ty_rhs⟩ => β[0] :]
    let m : PHashMap Nat Ty := (separate_fields (prev_fields ++ [(l, ty_fd)]) var_fields') ty_rhs
    m.insert id ty
  | _ => {}

/- old stuff that didn't work
    -- else if List.all fields (fun (k_fd, ty_fd) =>
    --   match ty_fd with
    --   | Ty.fvar _ => true 
    --   | _ => false 
    -- ) then  
    --   -- α[0] ↦ ∃ β[0] :: β[0] × α[1] ≤ ⟨nat_list⟩ => β[0]   
    --   -- succ * α[2] ≤ ∃ β[0] :: β[0] × α[1] ≤ ⟨nat_list⟩ => β[0]   
    --    -- this is garbage: circular environment: subst diverges   
    --   [(i, separate_fields [] fields (unroll (Ty.recur ty)))] 

    --   -- let rlabels := extract_record_labels (Ty.recur ty) 
    --   -- if List.all fields (fun (l, _) =>
    --   --   rlabels.contains l
    --   -- ) then

    --     -- let m : PHashMap Nat Ty := List.foldr (fun (l, ty_fd) env_ty =>
    --     --   match ty_fd with
    --     --   | .fvar id => env_ty.insert id Ty.top
    --     --   | _ => env_ty 
    --     -- ) {} fields 

    --     -- [(i, {})]
    --   -- else 
    --   --   []
    --   -- let ty' := List.foldr (fun (l, ty_fd) ty_acc =>
    --   --   match ty_fd with
    --   --   | .fvar _ => Ty.inter (Ty.field l Ty.bot) ty_acc
    --   --   | _ => ty_acc 
    --   -- ) Ty.top fields 
    --   -- -- unify i env_ty aim ty' (Ty.recur ty)
    --   -- []
    -- else
    --   []
-/


inductive Aim : Type
| adj | cen -- | max | min


/-
Aim.cen is safe when the free variables may be chosen (i.e. choosable).
Aim.max and Aim.min is necessary when the variables are fixed but unknown; they may not be chosen. 
-/
partial def unify (i : Nat) (env_ty : PHashMap Ty Ty) (aim : Aim) :
Ty -> Ty -> List (Nat × PHashMap Ty Ty)
| (.fvar id1), (.fvar id2) => 
  match (env_ty.find? (.fvar id1), env_ty.find? (.fvar id2)) with 
  | (.none, .none) => 
    -- ensure older unassigned free variables appear in simplified form
    if id1 < id2 then
      [
        (i, PHashMap.from_list [
          (.fvar id2, Ty.fvar id1)
        ])
      ]
    else if id1 > id2 then
      [
        (i, PHashMap.from_list [
          (.fvar id1, Ty.fvar id2)
        ])
      ]
    else
      []
  | (_, .some ty) => unify i env_ty aim (.fvar id1) ty 
  | (.some ty', _) => unify i env_ty aim ty' (.fvar id2) 

-- Notes on adjusting:
-- consider a function applied to an argument.
-- the paramater type might have type variables as subparts.
-- The corresponding suparts of the argument should unify with it, 
-- but not preclude the function from apply to other types, so it unifies with union.
-- therefore, adjusting types with union/intersection happens internally in unification.
-- adjusting in unification is a general way to handle substitution of intersection/union into variables
-- it generalized to type checking that can occur anywhere due to up/down propagation 
-- in contrast, for example, to simply substituting in union at application etc.
| .fvar id, ty  => 
  match env_ty.find? (.fvar id) with 
  | none => 
    let (i, ty_up) := (
      match aim with
      | .adj => (i + 1, Ty.inter ty (Ty.fvar i))
      | .cen => (i, ty)
      -- | .max => (i, ty)
      -- | .min => (i, Ty.bot)
    )
    [ 
      (i, PHashMap.from_list [
        (.fvar id, roll_corec id env_ty ty_up)
      ]) 
    ]
  | some ty' => unify i env_ty aim ty' ty 

| ty', .fvar id  => 
  match env_ty.find? (.fvar id) with 
  | none => 
    let (i, ty_low) := (
      match aim with
      | .adj => (i + 1, Ty.union ty' (Ty.fvar i))
      | .cen => (i, ty')
      -- | .max => (i, Ty.top)
      -- | .min => (i, ty')
    )
    [ 
      (i, PHashMap.from_list [
        (.fvar id, roll_recur id env_ty ty_low)
      ]) 
    ]
  | some ty => unify i env_ty aim ty' ty 

-- TODO: consider requiring normal form check to ensure safety
-- or using min/max to check both extremes
| .exis n ty_c1 ty_c2 ty1, ty2 =>
  let bound_start := i
  let (i, ids) := (i + n, (List.range n).map (fun j => i + j))
  let bound_end := i
  let is_old_var := (fun i' => i' < bound_start)
  let is_bound_var := (fun i' => bound_start <= i' && i' < bound_end)

  let args := ids.map (fun id => Ty.fvar id)
  let ty_c1 := Ty.instantiate 0 args ty_c1
  let ty_c2 := Ty.instantiate 0 args ty_c2
  let ty1 := Ty.instantiate 0 args ty1

  let op_fields := linearize_fields ty_c1

  let contexts := ( 
    match op_fields with 
    | some fields =>
      let is_recur_type := match ty_c2 with 
      | Ty.recur _ => true
      | _ => false
      let is_consistent_variable_record := List.all fields (fun (l, ty_fd) =>
        let rlabels := extract_record_labels (ty_c2) 
        rlabels.contains l &&
        (match ty_fd with | (Ty.fvar _) => true | _ => false)
      )
      if is_recur_type && is_consistent_variable_record then
        let ty_norm := normalize_fields fields
        [(i, PHashMap.from_list [(ty_norm, ty_c2)])]

      else []
    | none => (unify i (env_ty) Aim.cen ty_c1 ty_c2)
  )

  -- TODO: ensure that vacuous truth is sound
  -- given P |- Q, if P is incorreclty false, then P |- Q is incorrecly true (which is unsound)
  if contexts.isEmpty then
    -- vacuous truth; lhs constraint makes lhs empty
    [(i, {})]
  else
    List.bind contexts (fun (i, env_ty1) => 
    List.bind (unify i (env_ty;env_ty1) aim ty1 ty2) (fun (i, env_ty2) =>
      let env_ty_result := env_ty1;env_ty2
      -- safety check: ensure external free variables are not assigned to internal bound variables
      let is_result_safe := List.all env_ty_result.toList (fun (ty_key, ty_value) =>
        let var_keys := Ty.free_vars ty_key
        let var_values := Ty.free_vars ty_value
        (
          ( -- old vars can only bind to old vars or non-vars 
            not (var_keys.toList.any (fun (i, Unit.unit) => is_old_var i)) || 
            (var_values.toList.all (fun (i, Unit.unit) => is_old_var i))
          ) && 
          ( -- bound vars can only bind to bind vars or non-vars
            not (var_keys.toList.any (fun (i, Unit.unit) => is_bound_var i)) || 
            (var_values.toList.all (fun (i, Unit.unit) => is_bound_var i))
          )
          
        )
      )
      if is_result_safe then
        [(i, env_ty_result)]
      else
        []
    ))

| ty', .exis n ty_c1 ty_c2 ty =>
  let (i, args) := (i + n, (List.range n).map (fun j => .fvar (i + j)))

  let ty_c1 := Ty.instantiate 0 args ty_c1
  let ty_c2 := Ty.instantiate 0 args ty_c2
  let ty := Ty.instantiate 0 args ty
  List.bind (unify i env_ty aim ty' ty) (fun (i, env_ty1) =>
  List.bind (unify i (env_ty ; env_ty1) Aim.cen ty_c1 ty_c2) (fun (i, env_ty2) => 
    [ (i, env_ty1 ; env_ty2) ]
  ))

| ty1, .univ n ty_c1 ty_c2 ty2 =>
  let bound_start := i
  let (i, ids) := (i + n, (List.range n).map (fun j => i + j))
  let bound_end := i
  let is_old_var := (fun i' => i' < bound_start)
  let is_bound_var := (fun i' => bound_start <= i' && i' < bound_end)

  let args := ids.map (fun id => Ty.fvar id)
  let ty_c1 := Ty.instantiate 0 args ty_c1
  let ty_c2 := Ty.instantiate 0 args ty_c2
  let ty2 := Ty.instantiate 0 args ty2

  let contexts := (unify i (env_ty) Aim.cen ty_c1 ty_c2)

  if contexts.isEmpty then
    [(i, {})]
  else
    List.bind contexts (fun (i, env_ty1) => 
    List.bind (unify i (env_ty;env_ty1) aim ty1 ty2) (fun (i, env_ty2) =>
      let env_ty_result := env_ty1;env_ty2
      -- safety check: ensure external free variables are not assigned to internal bound variables
      let is_result_safe := List.all env_ty_result.toList (fun (ty_key, ty_value) =>
        let var_keys := Ty.free_vars ty_key
        let var_values := Ty.free_vars ty_value
        (
          ( -- old vars can only bind to old vars or non-vars 
            not (var_keys.toList.any (fun (i, Unit.unit) => is_old_var i)) || 
            (var_values.toList.all (fun (i, Unit.unit) => is_old_var i))
          ) && 
          ( -- bound vars can only bind to bind vars or non-vars
            not (var_keys.toList.any (fun (i, Unit.unit) => is_bound_var i)) || 
            (var_values.toList.all (fun (i, Unit.unit) => is_bound_var i))
          )
          
        )
      )
      if is_result_safe then
      -- if true then
        [(i, env_ty_result)]
      else
        []
    ))

| .univ n ty_c1 ty_c2 ty', ty =>
  let (i, args) := (i + n, (List.range n).map (fun j => .fvar (i + j)))
  let ty_c1 := Ty.instantiate 0 args ty_c1
  let ty_c2 := Ty.instantiate 0 args ty_c2
  let ty' := Ty.instantiate 0 args ty'
  List.bind (unify i env_ty aim ty' ty) (fun (i, env_ty1) =>
  List.bind (unify i (env_ty ; env_ty1) Aim.cen ty_c1 ty_c2) (fun (i, env_ty2) => 
    [ (i, env_ty1 ; env_ty2) ]
  ))

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
    unify i env_ty aim ty' ty
  else
    .nil 

| .field l' ty', .field l ty =>
  if l' = l then
    unify i env_ty aim ty' ty
  else
    .nil

| .case ty1 ty2', .case ty1' ty2 =>
  List.bind (unify i env_ty aim ty1' ty1) (fun (i, env_ty1) => 
  List.bind (unify i (env_ty ; env_ty1) aim ty2' ty2) (fun (i, env_ty2) =>
    [ (i, env_ty1 ; env_ty2) ]
  ))


| .recur ty', .recur ty =>
  if Ty.equal env_ty ty' ty then
    [ (i, {}) ]
  else
    -- unroll using rhs ty
    -- by induction hypothesis, ty' ≤ ty
    let ty' := [: ⟨ty'⟩ ↑ 0 // [μ β[0] => ⟨ty⟩]:]
    let ty := [: ⟨ty⟩ ↑ 0 // [μ β[0] => ⟨ty⟩]:]
    unify i env_ty Aim.cen ty' ty

| ty', .recur ty =>
  let ty' := (Ty.simplify (Ty.subst env_ty ty'))
  match (linearize_fields ty') with
  | .none => 
    unify i env_ty aim ty' (unroll (Ty.recur ty))
  | .some fields =>
    if List.any fields (fun (k_fd, ty_fd) =>
      match ty_fd with
      | Ty.tag _ _ => true 
      | Ty.top => true 
      | Ty.bot => true 
      | _ => false 
    ) then  
      unify i env_ty aim ty' (unroll (Ty.recur ty))
    else
      let ty_norm := normalize_fields fields
      match env_ty.find? ty_norm with
      | .some ty_cache => unify i env_ty Aim.cen ty_cache (Ty.recur ty)
      | .none => []

| ty', .corec ty1 =>
  -- reduce to "arrow-normal-form" for propagation purposes
  match rewrite_function_type (.corec ty1) with
  | .some ty_rw => 
    unify i env_ty aim ty' ty_rw
  | .none => .nil

| .corec ty1, ty =>
  -- reduce to "arrow-normal-form" for propagation purposes
  match rewrite_function_type (.corec ty1) with
  | .some ty_rw => 
    unify i env_ty aim ty_rw ty 
  | .none => .nil

-- | .corec ty1, Ty.case ty2 ty3 =>
--   if wellformed_unroll_type env_ty ty2 || wellformed_unroll_type env_ty ty3 then
--     unify i env_ty aim (unroll (Ty.corec ty1)) (Ty.case ty2 ty3)
--   else
--     match rewrite_function_type (.corec ty1) with
--     | .some ty' => 
--       unify i env_ty aim ty' (Ty.case ty2 ty3)
--     | .none => .nil

| .union ty1 ty2, ty => 
  List.bind (unify i env_ty aim ty1 ty) (fun (i, env_ty1) => 
  List.bind (unify i (env_ty ; env_ty1) aim ty2 ty) (fun (i, env_ty2) =>
    [ (i, env_ty1 ; env_ty2) ]
  ))

| ty, .union ty1 ty2 => 
  (unify i env_ty aim ty ty1) ++ (unify i env_ty aim ty ty2)


| ty, .inter ty1 ty2 => 
  List.bind (unify i env_ty aim ty ty1) (fun (i, env_ty1) => 
  List.bind (unify i (env_ty ; env_ty1) aim ty ty2) (fun (i, env_ty2) =>
    [ (i, env_ty1 ; env_ty2) ]
  ))

| .inter ty1 ty2, ty => 
  (unify i env_ty aim ty1 ty) ++ (unify i env_ty aim ty2 ty)

| _, _ => .nil 

def unify_all (i : Nat) (cs : List (Ty × Ty)) : List (Nat × PHashMap Ty Ty) := 
  List.foldl (fun u_env_ty1 => fun (ty_c1, ty_c2) => 
    List.bind u_env_ty1 (fun (i, env_ty1) => 
    List.bind (unify i env_ty1 Aim.cen ty_c1 ty_c2) (fun (i, env_ty2) =>
      [ (i, env_ty1 ; env_ty2) ]
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


partial def unify_reduce (i : Nat) (ty1) (ty2) (ty_result) :=
  (unify i {} Aim.cen ty1 ty2).foldl (fun acc => fun  (_, env_ty) =>
    Ty.simplify ((Ty.subst env_ty (Ty.union ty_result acc)))
  ) (Ty.bot)

partial def unify_decide (i : Nat) (ty1) (ty2) :=
  not (unify i {} Aim.cen ty1 ty2).isEmpty

partial def unify_simple (i : Nat) (ty1) (ty2) :=
  (unify i {} Aim.cen ty1 ty2)


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

partial def Tm.generalize (fids : List Nat) (start : Nat) : Tm -> Tm
| .hole => Tm.hole 
| .unit => Tm.unit 
| .bvar id => Tm.bvar id 
| .fvar id => 
  match (fids.enumFrom start).find? (fun (_, fid) => fid == id) with
  | .some (bid, _) => .bvar bid
  | .none => .fvar id 
| .tag l t => .tag l (Tm.generalize fids start t) 
| .record fds =>
  Tm.record (List.map (fun (l, t) =>
    (l, Tm.generalize fids start t)
  ) fds)
| .func fs =>
  Tm.func (List.map (fun (tp, tb) =>
    let n := match pattern_wellformed 0 tp with
    | .some n => n 
    | .none => 0 
    let tp := Tm.generalize fids (start + n) tp 
    let tb := Tm.generalize fids (start + n) tb
    (tp, tb)
  ) fs)
| .proj t l => 
  Tm.proj (Tm.generalize fids start t) l
| .app t1 t2 =>
  Tm.app 
    (Tm.generalize fids start t1) 
    (Tm.generalize fids start t2)
| .letb ty1 t1 t2 =>
  Tm.letb ty1 
    (Tm.generalize fids start t1)
    (Tm.generalize fids (start + 1) t2)
| .fix t =>
  Tm.fix (Tm.generalize fids start t)


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
  Tm.func (List.map (fun (tp, tb) =>
    let n := match pattern_wellformed 0 tp with
    | .some n => n 
    | .none => 0 
    let tp := Tm.instantiate (start + n) args tp 
    let tb := Tm.instantiate (start + n) args tb
    (tp, tb)
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


structure Guide where
  env_tm : PHashMap Nat Ty
  ty_expected : Ty
deriving Repr

structure Contract where
  i : Nat
  env_ty : PHashMap Ty Ty 
  guides : List (Nat × Guide) -- [..., (hole variable, guide), ...]
  t : Tm
  ty : Ty 
deriving Repr

partial def infer (i : Nat) (env_ty : PHashMap Ty Ty) (env_tm : PHashMap Nat Ty) (aim : Aim) (t : Tm) (ty : Ty) : 
List Contract := 
match t with
| Tm.hole => 
  let guide : Guide := ⟨env_tm, ty⟩
  [{
      i := i + 1, 
      env_ty := {}, guides := [(i, guide)], 
      t := (Tm.fvar i), ty := ty
  }] 
| Tm.unit => 
  List.bind (unify i env_ty aim Ty.unit ty) (fun (i, env_ty_x) => 
    [{i := i, env_ty := env_ty_x, guides := [], t := t, ty := Ty.unit}]
  )
| Tm.bvar _ => .nil 
| Tm.fvar id =>
  match (env_tm.find? id) with 
    | .some ty' => 
      List.bind (unify i env_ty aim ty' ty) (fun (i, env_ty_x) =>
        [{
          i := i, 
          env_ty := env_ty_x, guides := [], 
          t := t, ty := ty'
        }]
      )
    | .none => .nil 

| .tag l t1 =>   
  let (i, ty1) := (i + 1, Ty.fvar i)
  List.bind (unify i env_ty aim (Ty.tag l ty1) ty) (fun (i, env_ty1) =>
  List.bind (infer i env_ty env_tm aim t1 ty1) (fun ⟨i, env_ty2, guides_t1, t1', ty1'⟩ =>
    [⟨
      i, 
      env_ty1;env_ty2, guides_t1, 
      Tm.tag l t1', 
      Ty.tag l ty1'
    ⟩]
  ))

| .record fds =>
  let (i, trips) := List.foldr (fun (l, t1) (i, ty_acc) =>
    (i + 1, (l, t1, (Ty.fvar i)) :: ty_acc)
  ) (i, []) fds

  let ty_init := Ty.top

  let ty' := List.foldr (fun (l, _, ty1) ty_acc => 
    Ty.inter (Ty.field l ty1) ty_acc 
  ) ty_init trips 

  let u_env_ty1 := unify i env_ty aim ty' ty 

  let f_step := (fun (l, t1, ty1) acc =>
    List.bind acc (fun ⟨i, env_ty_acc, guides_acc, t_acc, ty_acc⟩ =>
    List.bind (infer i (env_ty;env_ty_acc) env_tm aim t1 ty1) (fun ⟨i, env_ty_x, guides_t1, t1', ty1'⟩ =>
      match t_acc with
      | Tm.record fds_acc =>
        [⟨
          i,
          env_ty_acc;env_ty_x,
          guides_acc ++ guides_t1,
          Tm.record ((l, t1') :: fds_acc),
          Ty.inter (Ty.field l ty1') ty_acc
        ⟩]
      | _ => .nil
    ))
  )

  let init := u_env_ty1.map fun (i, env_ty1) => ⟨i, env_ty1, [], Tm.record [], Ty.top⟩
  List.foldr f_step init trips

| .func fs =>
  let (i, fs_typed) := List.foldr (fun (p, b) (i, ty_acc) =>
    (i + 2, (p, Ty.fvar i, b, Ty.fvar (i + 1)) :: ty_acc)
  ) (i, []) fs

  let case_init := Ty.top

  let (i, ty') := List.foldr (fun (p, ty_p, b, ty_b) (i, ty_acc) => 
    (i, Ty.inter (Ty.case ty_p ty_b) ty_acc) 
  ) (i, case_init) fs_typed 

  let u_env_ty1 := unify i env_ty aim ty' ty 

  let f_step := (fun (p, ty_p, b, ty_b) acc =>
    List.bind acc (fun ⟨i, env_ty_acc, guides_acc, t_acc, ty_acc⟩ =>
    List.bind (pattern_wellformed 0 p).toList (fun n =>

    let env_pat : PHashMap Nat Ty := (List.range n).foldl (init := {}) (fun env_pat j => 
      let tm_key := (i + (2 * j))
      let ty_x := Ty.fvar (i + (2 * j) + 1)
      (env_pat.insert tm_key ty_x)
    )
    let i := i + (2 * n)

    let fids := env_pat.toList.map (fun (k, _) => k)
    let list_tm_x := env_pat.toList.map (fun (k, _) => (Tm.fvar k))

    let p := Tm.instantiate 0 list_tm_x p 
    let b := Tm.instantiate 0 list_tm_x b  
    List.bind (
      infer i (env_ty;env_ty_acc) (env_tm ; env_pat) Aim.cen p ty_p
    ) (fun ⟨i, env_ty_p, _, _, ty_p'⟩ =>
    List.bind (
      infer i (env_ty;env_ty_acc;env_ty_p) (env_tm ; env_pat) aim b ty_b
    ) (fun ⟨i, env_ty_b, guides_b, b', ty_b'⟩ =>
      match t_acc with
      | Tm.func cases_acc =>
        [⟨
          i,
          env_ty_acc;env_ty_p;env_ty_b,
          guides_acc ++ guides_b,
          Tm.func ((p, Tm.generalize fids 0 b') :: cases_acc),
          Ty.simplify (Ty.inter (Ty.case ty_p' ty_b') ty_acc)
        ⟩]
      | _ => .nil
    ))))
  )

  let init := u_env_ty1.map fun (i, env_ty1) => ⟨i, env_ty1, [], Tm.func [], Ty.top⟩
  List.foldr f_step init fs_typed

| .proj t1 l =>
  List.bind (infer i env_ty env_tm aim t1 (Ty.field l ty)) (fun ⟨i, env_ty1, guides_t1, t1', ty1'⟩ =>
  let (i, ty') := (i + 1, Ty.fvar i)
  List.bind (unify i (env_ty;env_ty1) aim ty1' (Ty.field l ty')) (fun (i, env_ty2) =>
    [⟨i, env_ty1;env_ty2, guides_t1, Tm.proj t1' l, ty'⟩]
  ))

| .app t1 t2 =>
  let (i, ty2) := (i + 1, Ty.fvar i)
  let (i, ty') := (i + 1, Ty.fvar i)
  -- infer i env_ty env_tm aim t1 [: ⊤ :]
  -- infer i env_ty env_tm aim t1 (Ty.case ty2 ty)
  List.bind (infer i env_ty env_tm aim t1 (Ty.case ty2 ty)) (fun ⟨i, env_ty1, guides_t1, t1', ty1⟩ =>
  List.bind (infer i (env_ty;env_ty1) env_tm aim t2 ty2) (fun ⟨i, env_ty2, guides_t2, t2', ty2'⟩ =>
  List.bind (unify i (env_ty;env_ty1;env_ty2) aim ty1 (Ty.case ty2' ty')) (fun (i, env_ty3) =>
    [⟨i, env_ty1;env_ty2;env_ty3, guides_t1 ++ guides_t2, Tm.app t1' t2', ty'⟩]
  )))


| .letb ty1 t1 t => 
  let free_var_boundary := i
  List.bind (infer i env_ty env_tm Aim.cen t1 ty1) (fun ⟨i, env_ty1, guides_t1, t1', ty1'⟩ =>

  -- prevent overgeneralization by filtering
  let ty1' := Ty.reduce (env_ty;env_ty1) ty1'
  let fvs := List.filter (. >= free_var_boundary) (
    (Ty.free_vars ty1').toList.reverse.bind (fun (k, _) => [k])
  )
  let ty1' := if fvs.isEmpty then ty1' else [: ∀ ⟨fvs.length⟩ => ⟨Ty.generalize fvs 0 ty1'⟩ :]
  let fids := [i]
  let (i, x, env_tmx) := (i + 1, Tm.fvar i, PHashMap.from_list [(i, ty1')]) 
  let t := Tm.instantiate 0 [x] t 

  List.bind (infer i (env_ty;env_ty1) (env_tm ; env_tmx) aim t ty) (fun ⟨i, env_ty', guides_t, t', ty'⟩ =>
    [ ⟨i, env_ty1;env_ty', guides_t1 ++ guides_t, .letb ty1' t1' (Tm.generalize fids 0 t'), ty'⟩ ]
  ))

| .fix t1 =>
  List.bind (infer i env_ty env_tm Aim.adj t1 (Ty.case [: ⊥ :] ty)) (fun ⟨i, env_ty1, guides_t1, t1', ty1'⟩ =>
  let (i, ty_prem) := (i + 1, Ty.fvar i) 
  let (i, ty_conc) := (i + 1, Ty.fvar i) 
  List.bind (unify i (env_ty;env_ty1) Aim.adj ty1' (.case ty_prem ty_conc)) (fun (i, env_ty2) =>

    let ty_prem := Ty.reduce (env_ty;env_ty1;env_ty2) ty_prem 
    let ty_conc := Ty.reduce (env_ty;env_ty1;env_ty2) ty_conc

    let fvs := (Ty.free_vars ty_prem).toList.bind (fun (k, _) => [k])

    let ty' := [: ν β[0] => 
      (∀ ⟨fvs.length⟩ :: 
        β[⟨fvs.length⟩] ≤ ⟨Ty.generalize fvs 0 ty_prem⟩ => 
        ⟨Ty.generalize fvs 0 ty_conc⟩ 
      )
    :]
    -- constrain that ty' <= ty_prem is built into inductive type
    [ ⟨i, env_ty1;env_ty2, guides_t1, Tm.fix t1', ty'⟩ ]
  ))

partial def PHashMap.intersect (m1 : PHashMap Nat Unit) (m2 : PHashMap Nat Unit) :=
  PHashMap.from_list (m1.toList.filter (fun (id, _) => m2.contains id))

partial def infer_reduce_wt (i : Nat) (t : Tm) (ty : Ty): Ty :=
  (infer i {} {} Aim.adj t ty).foldl (fun acc => fun  ⟨_, env_ty, _, _, ty'⟩ =>

    let ty' := Ty.simplify ((Ty.subst env_ty (Ty.union acc ty')))
    let pos_neg_set := PHashMap.intersect (Ty.signed_free_vars true ty') (Ty.signed_free_vars false ty')

    let fvs := pos_neg_set.toList.reverse.bind (fun (k, _) => [k])
    if fvs.isEmpty then
      Ty.simplify (Ty.subst_default true ty')
    else
      Ty.simplify (Ty.subst_default true [: ∀ ⟨fvs.length⟩ => ⟨Ty.generalize fvs 0 ty'⟩ :])

  ) (Ty.bot)



partial def infer_reduce (i : Nat) (t : Tm) : Ty := infer_reduce_wt i t [: ⊤ :]

structure Work where
  cost : Nat
  i : Nat
  guides : PHashMap Nat Guide
  patches : PHashMap Nat Tm 
  t : Tm
deriving Repr

-- ooga
#eval infer_reduce 0 [:
  fix(λ y[0] => λ[
  for zero;() => nil;(),
  for succ;y[0] => cons;(y[1] y[0])
  ])
:]

-- #eval infer_reduce 0 [:
--   let y[0] = fix(λ y[0] => λ[
--   for zero;() => nil;(),
--   for succ;y[0] => cons;(y[1] y[0])
--   ]) =>
--   y[0]
-- :]

-- #eval infer_reduce 0 [:
--   let y[0] = fix(λ y[0] => λ[
--   for zero;() => nil;(),
--   for succ;y[0] => cons;(y[1] y[0])
--   ]) =>
--   (y[0] (zero;()))
-- :]


-- booga
def nat_to_list := [: 
  ν β[0] => 
    (zero*@ -> nil*@) ∧ 
    (∀ 2 :: β[2] ≤ β[0] -> β[1] => 
      succ*β[0] -> cons*β[1])
:]

-- TODO
-- expected: cons;()
#eval infer_reduce 0 [:
  let y[0] : ⟨nat_to_list⟩ = _ =>
  (y[0] (zero;()))
:]

----------------------------------------


def Work.le (x y: Work): Bool := x.cost <= y.cost

def Work.Queue := BinomialHeap Work Work.le

partial def Tm.cost : Tm -> Nat
| hole => 1 
| unit => 1 
| bvar id => 1 
| fvar id => 1
| tag l t => 1 + (Tm.cost t)
| record entries => 
  List.foldl (fun cost' (l, t) => cost' + (Tm.cost t)) 1 entries
| func cases =>
  List.foldl (fun cost' (p, t_b) => cost' + (Tm.cost t_b)) 1 cases
| proj t l => 1 + (Tm.cost t)
| app t1 t2 => 1 + (Tm.cost t1) + (Tm.cost t2)
| letb ty t1 t2 => 1 + (Tm.cost t1) + (Tm.cost t2)
| .fix t => 1 + (Tm.cost t)

partial def Tm.subst (m : PHashMap Nat Tm) : Tm -> Tm 
| hole => hole 
| unit => unit 
| bvar id => bvar id 
| fvar id => (match m.find? id with
  | some t => Tm.subst m t 
  | none => .fvar id
)
| tag l t => tag l (Tm.subst m t)
| record entries => 
  let entries' := List.map (fun (l, t) => (l, Tm.subst m t)) entries 
  record entries'
| func cases =>
  let cases' := List.map (fun (p, t_b) => 
    (p, Tm.subst m t_b)
  ) cases 
  func cases'
| proj t l => proj (Tm.subst m t) l
| app t1 t2 => app (Tm.subst m t1) (Tm.subst m t2)
| letb ty t1 t2 => letb ty (Tm.subst m t1) (Tm.subst m t2)
| .fix t => Tm.fix (Tm.subst m t)


-- (tag labels, field labels)
partial def extract_labels : Ty -> (List String × List String)
| .bvar id => ([], []) 
| .fvar id => ([], [])
| .unit => ([], []) 
| .bot => ([], [])
| .top => ([], [])
| .tag l ty => 
  let (ls_t, ls_f) := extract_labels ty
  (l :: ls_t, ls_f) 
| .field l ty => 
  let (ls_t, ls_f) := extract_labels ty
  (ls_t, l :: ls_f) 
| .union ty1 ty2 => 
  let (ls_t1, ls_f1) := extract_labels ty1
  let (ls_t2, ls_f2) := extract_labels ty2
  (ls_t1 ++ ls_t2, ls_f1 ++ ls_f2) 
| .inter ty1 ty2 => 
  let (ls_t1, ls_f1) := extract_labels ty1
  let (ls_t2, ls_f2) := extract_labels ty2
  (ls_t1 ++ ls_t2, ls_f1 ++ ls_f2) 
| .case ty1 ty2 => 
  let (ls_t1, ls_f1) := extract_labels ty1
  let (ls_t2, ls_f2) := extract_labels ty2
  (ls_t1 ++ ls_t2, ls_f1 ++ ls_f2) 
| .exis n ty_c1 ty_c2 ty =>
  let (ls_tc1, ls_fc1) := extract_labels ty_c1
  let (ls_tc2, ls_fc2) := extract_labels ty_c2
  let (ls_t, ls_f) := extract_labels ty
  (ls_tc1 ++ ls_tc2 ++ ls_t, ls_fc1 ++ ls_fc2 ++ ls_f) 
| .univ n ty_c1 ty_c2 ty => 
  let (ls_tc1, ls_fc1) := extract_labels ty_c1
  let (ls_tc2, ls_fc2) := extract_labels ty_c2
  let (ls_t, ls_f) := extract_labels ty
  (ls_tc1 ++ ls_tc2 ++ ls_t, ls_fc1 ++ ls_fc2 ++ ls_f) 
| .recur ty =>
  extract_labels ty
| .corec ty =>
  extract_labels ty


partial def enumerate_fields : List String -> List (List (String × Tm))
| [] => []
| l :: ls =>
  (enumerate_fields ls).map (fun fields => (l, Tm.hole) :: fields)

partial def enumerate_cases : List String -> List (List (Tm × Tm))
| [] => []
| l :: ls =>
  (enumerate_cases ls).map (fun cases => ([: ⟨l⟩;y[0] :], [: _ :]) :: cases)

partial def join_functions (t1 : Tm) (t2 : Tm) : List Tm := match t1, t2 with
| Tm.func cases1, Tm.func cases2 => [Tm.func (cases1 ++ cases2)]
| _, _ => []

partial def enumerate (i : Nat) (env_tm : PHashMap Nat Ty) (ty : Ty) : List Tm :=
  let (ls_t, ls_f) := (extract_labels ty)
  let tags := ls_t.map (fun l => Tm.tag l Tm.hole)

  let fields := enumerate_fields ls_f
  let records := fields.map (fun fds => Tm.record fds)

  let cases := enumerate_cases ls_t
  let functions := (
    [: λ y[0] => _ :] :: 
    (cases.map (fun cases => Tm.func cases))
  )

  [: () :] ::
  tags ++
  records ++
  functions ++
  [ [: let y[0] = _ => _ :] ] ++
  [ [: fix _ :] ] ++
  List.bind env_tm.toList (fun (x, ty) =>
    let (_, ls) := extract_labels ty
    let var := (Tm.fvar x)
    let application := [: let y[0] = (⟨Tm.fvar x⟩ _) => _ :] 
    let projections := ls.map (fun l =>
      [: let y[0] = (⟨Tm.fvar x⟩/⟨l⟩) => _ :] 
    )
    var :: application :: projections
  )


-- | hole : Tm 
-- | unit : Tm
-- | bvar : Nat -> Tm 
-- | fvar : Nat -> Tm 
-- | tag : String -> Tm -> Tm
-- | record : List (String × Tm) -> Tm
-- | func : List (Tm × Ty × Tm) -> Tm
-- | proj : Tm -> String -> Tm
-- | app : Tm -> Tm -> Tm
-- | letb : Ty -> Tm -> Tm -> Tm
-- | fix : Tm -> Tm






#check BinomialHeap.ofList
#check BinomialHeap.merge

partial def synthesize_loop (queue : Work.Queue) : Option Tm := 
  Option.bind (queue.deleteMin) (fun (work, queue') =>
    if work.guides.isEmpty then
      some (Tm.subst work.patches work.t)
    else 
      let queue_ext := BinomialHeap.ofList Work.le (
        List.bind work.guides.toList (fun (id, guide) =>
          let hypotheses := enumerate work.i guide.env_tm guide.ty_expected
          List.bind hypotheses (fun h =>
          let contracts := (infer work.i {} guide.env_tm Aim.cen h guide.ty_expected)
          List.bind contracts (fun ⟨i, _, guides, t, _⟩ =>
            let patch := t
            [
              {
                cost := work.cost + (Tm.cost h),
                i := i,
                guides := work.guides.erase id ; (PHashMap.from_list guides),
                patches := work.patches.insert id patch 
                t := work.t 
              }

            ]
          ))
        ) 
      )

      let queue'' := BinomialHeap.merge queue' queue_ext

      synthesize_loop queue''
  )



partial def synthesize (t : Tm) : Option Tm := 
  let contracts := infer 0 {} {} Aim.cen t [: ∃ 1 => β[0] :]
  let works : List Work := contracts.map (fun contract =>
    {
      cost := (Tm.cost t), i := contract.i, 
      guides := PHashMap.from_list contract.guides, 
      patches := {},
      t := contract.t
    }
  )
  let queue := List.foldl (fun queue work =>
    queue.insert work
  ) BinomialHeap.empty works

  (synthesize_loop queue) 

partial def synth_reduce (t : Tm) : Tm := 
  match synthesize t with
  | some t => t
  | none => Tm.hole