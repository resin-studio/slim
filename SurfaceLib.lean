import Std.Data.BinomialHeap
import Init.Data.Hashable
import Lean.Data.PersistentHashMap

open Std

inductive Ty : Type
| var : String -> Ty
| unit : Ty
| bot : Ty
| top : Ty
| tag : String -> Ty -> Ty
| field : String -> Ty -> Ty
| union : Ty -> Ty -> Ty
| inter : Ty -> Ty -> Ty
| case : Ty -> Ty -> Ty
| univ : List String -> Ty -> Ty -> Ty -> Ty
| exis : List String -> Ty -> Ty -> Ty -> Ty
| recur : String -> Ty -> Ty
| corec : String -> Ty -> Ty
deriving Repr, Inhabited, Hashable, BEq
#check List.repr

protected partial def Ty.repr (ty : Ty) (n : Nat) : Format :=
match ty with
| .var id => id
| .unit => "@" 
| .bot => "⊥" 
| .top => "⊤" 
| .tag l ty1 => 
  (l ++ "*" ++ (Ty.repr ty1 n))
| .field l ty1 => 
  Format.bracket "(" (l ++ " : " ++ (Ty.repr ty1 n)) ")"

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
| .univ names ty_c1 ty_c2 ty_pl =>
  let bound_names := (Format.bracket "("
    (Format.joinSep names (", " ++ Format.line))
  ")")
  if (ty_c1, ty_c2) == (Ty.unit, Ty.unit) then
    Format.bracket "(" (
      "∀ " ++ bound_names ++ " ." ++ Format.line ++ 
      (Ty.repr ty_pl n)
    ) ")"
  else
    Format.bracket "(" (
      "∀ " ++ bound_names ++ " ." ++ Format.line ++ 
      (Ty.repr ty_pl n) ++ " | " ++
      (Ty.repr ty_c1 n) ++ " ≤ " ++ (Ty.repr ty_c2 n)
    ) ")"
| .exis names ty_c1 ty_c2 ty_pl =>
  let bound_names := (Format.bracket "("
    (Format.joinSep names (", " ++ Format.line))
  ")")
  if (ty_c1, ty_c2) == (Ty.unit, Ty.unit) then
    Format.bracket "(" (
      "∃ " ++ bound_names ++ " ." ++ Format.line ++ 
      (Ty.repr ty_pl n)
    ) ")"
  else
    Format.bracket "(" (
      "∃ " ++ bound_names ++ " ." ++ Format.line ++ 
      (Ty.repr ty_pl n) ++ " | " ++
      (Ty.repr ty_c1 n) ++ " ≤ " ++ (Ty.repr ty_c2 n)
    ) ")"
| .recur name ty1 =>
  Format.bracket "(" (
    "μ " ++ name ++  " . " ++ (Ty.repr ty1 n)
  ) ")"
| .corec name ty1 =>
  Format.bracket "(" (
    "ν " ++ name ++  " . " ++ (Ty.repr ty1 n)
  ) ")"

instance : Repr Ty where
  reprPrec := Ty.repr


inductive Tm : Type
| hole : Tm 
| unit : Tm
| bvar : String -> Tm 
| fvar : String -> Tm 
| tag : String -> Tm -> Tm
| record : List (String × Tm) -> Tm
| func : List (Tm × Tm) -> Tm
| proj : Tm -> String -> Tm
| app : Tm -> Tm -> Tm
| letb : String -> Option Ty -> Tm -> Tm -> Tm
| fix : Tm -> Tm
deriving Repr, Inhabited, BEq

def indent(n : Nat) : String :=
  Nat.fold (fun | _, acc => acc ++ "  " ) n ""


declare_syntax_cat slm
syntax:100 num : slm 
syntax:100 ident : slm
syntax "(" slm,+ ")" : slm 
-- type
-- syntax:90 "β["slm:100"]" : slm
-- syntax:90 "α["slm:100"]" : slm
syntax:90 "@" : slm
syntax:90 "⊥" : slm
syntax:90 "⊤" : slm
syntax:90 slm:100 "*" slm:90 : slm
syntax:90 slm:100 ":" slm:90 : slm
syntax:50 slm:51 "->" slm:50 : slm
syntax:60 slm:61 "∨" slm:60 : slm
syntax:60 slm:61 "+" slm:60 : slm
syntax:70 slm:71 "∧" slm:70 : slm
syntax:70 slm:71 "×" slm:70 : slm
syntax:40 "∃" slm "." slm:40 "|" slm "≤" slm: slm 
syntax:40 "∃" slm "." slm:40 : slm 
syntax:40 "∀" slm slm:40 "|" slm "≤" slm : slm 
syntax:40 "∀" slm slm:40 : slm 
syntax:80 "μ " slm slm : slm 
syntax:80 "ν " slm slm : slm 

--term
syntax:30 "_" : slm
syntax:30 "()" : slm
-- syntax:30 "y[" slm:90 "]": slm
-- syntax:30 "x[" slm:90 "]" : slm
syntax:30 slm:100 ";" slm:30 : slm
syntax:30 slm:100 ":=" slm:30 : slm
syntax:30 "(" slm "," slm ")" : slm
syntax:30 "σ" slm : slm
syntax:20 "for" slm:30 ":" slm "=>" slm:20 : slm 
syntax:20 "for" slm:30 "=>" slm:20 : slm 
syntax:20 "λ" slm:30 ":" slm "=>" slm:20 : slm 
syntax:20 "λ" slm:30 "=>" slm:20 : slm 
syntax:30 "λ" slm : slm 
syntax:30 slm:30 "/" slm:100 : slm 
syntax:30 "(" slm:30 slm:30 ")" : slm 
syntax:30 "let" slm ":" slm:30 "=" slm:30 "=>" slm:30 : slm 
syntax:30 "let" slm "=" slm:30 "=>" slm:30 : slm 
syntax:30 "fix " slm:30 : slm 

syntax:50 slm:50 "⊆" slm:51 : slm

syntax "(" slm ")" : slm

syntax "⟨" term "⟩" : slm 

syntax "[: " slm ":]" : term

macro_rules
-- terminals
| `([: $n:num :]) => `($n)
| `([: $a:ident:]) => `(Ty.var $(Lean.quote (toString a.getId)))
-- context 
| `([: ($x:slm) :]) => `([ match [: $x :] with | .var name => name | _ => "" ])
| `([: ($x,$xs:slm,*) :]) => `([: ( $x ) :] ++ [: ($xs,*):])
-- Ty 
| `([: @ :]) => `(Ty.unit)
| `([: ⊥ :]) => `(Ty.bot)
| `([: ⊤ :]) => `(Ty.top)
| `([: $a * $b:slm :]) => `(Ty.tag [: $a :] [: $b :])
| `([: $a : $b:slm :]) => `(Ty.field [: $a :] [: $b :])
| `([: $a -> $b :]) => `(Ty.case [: $a :] [: $b :])
| `([: $a ∨ $b :]) => `(Ty.union [: $a :] [: $b :])
| `([: $a + $b :]) => `(Ty.union (Ty.tag "inl" [: $a :]) (Ty.tag "inr" [: $b :]))
| `([: $a ∧ $b :]) => `(Ty.inter [: $a :] [: $b :])
| `([: $a × $b :]) => `(Ty.inter (Ty.field "l" [: $a :]) (Ty.field "r" [: $b :]))
| `([: ∀ $a $d | $b ≤ $c :]) => `(Ty.univ [: $a :] [: $b :] [: $c :] [: $d :])
| `([: ∀ $a:slm $b:slm :]) => `(Ty.univ [: $a :] [: @ :] [: @ :] [: $b :] )
| `([: ∃ $a . $d | $b ≤ $c  :]) => `(Ty.exis [: $a :] [: $b :] [: $c :] [: $d :])
| `([: ∃ $a:slm . $b:slm :]) => `(Ty.exis [: $a :] [: @ :] [: @ :] [: $b :] )
| `([: μ 1 . $a :]) => `(Ty.recur [: $a :])
| `([: ν 1 . $a :]) => `(Ty.corec [: $a :])
--Tm
| `([: _ :]) => `(Tm.hole)
| `([: () :]) => `(Tm.unit)
-- | `([: y[$n] :]) => `(Tm.bvar [: $n :])
-- | `([: x[$n] :]) => `(Tm.var [: $n :])
| `([: $a ; $b :]) => `(Tm.tag [: $a :] [: $b :])
| `([: $a := $b :]) => `(([: $a :], [: $b :]))
| `([: for $b => $d :]) => `(([: $b :], [: $d :]))
| `([: σ $a :]) => `(Tm.record [: $a :])
| `([: ( $a , $b ) :]) => `(Tm.record [("l", [: $a :]), ("r", [:$b :])])
| `([: λ $b => $d :]) => `(Tm.func [([: $b :], [: $d :])])
| `([: λ $a :]) => `(Tm.func [: $a :])
| `([: $a / $b :]) => `(Tm.proj [: $a :] [: $b :])
| `([: ($a $b) :]) => `(Tm.app [: $a :] [: $b :])
| `([: let $name : $a = $b => $c :]) => `(Tm.letb [: $name :] (Option.some [: $a :]) [: $b :] [: $c :])
| `([: let $name = $b => $c :]) => `(Tm.letb [: $name :] Option.none [: $b :] [: $c :])
| `([: fix $a :]) => `(Tm.fix [: $a :])

-- generic
  | `([: ($a) :]) => `([: $a :])

--escape 
  | `([: ⟨ $e ⟩ :]) => pure e


#check [: (x) :]
#eval [: ∀ (thing) thing :]

-------------------


protected partial def Tm.repr (t : Tm) (n : Nat) : Format :=
match t with
| .hole => 
  "_"
| .unit =>
  "()"
| .bvar id => id
| .fvar id => id
| .tag l t1 =>
  l ++ ";" ++ (Tm.repr t1 n)
| record [("l", l), ("r", r)] =>
  let _ : ToFormat Tm := ⟨fun t1 => Tm.repr t1 n ⟩
  Format.bracket "(" (Format.joinSep [l, r] ("," ++ Format.line)) ")"
| record fds =>
  let _ : ToFormat (String × Tm) := ⟨fun (l, t1) =>
    l ++ " := " ++ Tm.repr t1 n ⟩
  "σ" ++ Format.bracket "[" (Format.joinSep fds ("," ++ Format.line)) "]"
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
| .letb name op_ty1 t1 t2 =>
  match op_ty1 with
  | some ty1 =>
    "let " ++ name ++ " : " ++ (Ty.repr ty1 n) ++ " = " ++  (Tm.repr t1 n) ++ " =>" ++
    Format.line  ++ (Tm.repr t2 n) 
  | none =>
    "let " ++ name ++ " = " ++  (Tm.repr t1 n) ++ " =>" ++
    Format.line  ++ (Tm.repr t2 n) 
| .fix t1 =>
  Format.bracket "(" ("fix " ++ (Tm.repr t1 n)) ")"

instance : Repr Tm where
  reprPrec := Tm.repr