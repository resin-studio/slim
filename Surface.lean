import Std.Data.BinomialHeap
import Init.Data.Hashable
import Lean.Data.PersistentHashMap

-- import Normal

open Std

namespace Surface

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
        "∀ " ++ bound_names ++ Format.line ++ 
        (Ty.repr ty_pl n)
      ) ")"
    else
      Format.bracket "(" (
        "∀ " ++ bound_names ++  Format.line ++ 
        (Ty.repr ty_pl n) ++ " | " ++
        (Ty.repr ty_c1 n) ++ " ≤ " ++ (Ty.repr ty_c2 n)
      ) ")"
  | .exis names ty_c1 ty_c2 ty_pl =>
    let bound_names := (Format.bracket "("
      (Format.joinSep names (", " ++ Format.line))
    ")")
    if (ty_c1, ty_c2) == (Ty.unit, Ty.unit) then
      Format.bracket "(" (
        "∃ " ++ bound_names ++ Format.line ++ 
        (Ty.repr ty_pl n)
      ) ")"
    else
      Format.bracket "(" (
        "∃ " ++ bound_names ++ Format.line ++ 
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



  declare_syntax_cat surf
  syntax:100 num : surf 
  syntax:100 ident : surf
  syntax "[" surf,+ "]" : surf 
  -- type
  syntax:90 "@" : surf
  syntax:90 "⊥" : surf
  syntax:90 "⊤" : surf
  syntax:90 surf:100 "*" surf:90 : surf
  syntax:90 surf:100 ":" surf:90 : surf
  syntax:50 surf:51 "->" surf:50 : surf
  syntax:60 surf:61 "∨" surf:60 : surf
  syntax:60 surf:61 "+" surf:60 : surf
  syntax:70 surf:71 "∧" surf:70 : surf
  syntax:70 surf:71 "×" surf:70 : surf
  syntax:40 "∃" surf surf:40 "|" surf "≤" surf: surf 
  syntax:40 "∃" surf surf:40 : surf 
  syntax:40 "∀" surf surf:40 "|" surf "≤" surf : surf 
  syntax:40 "∀" surf surf:40 : surf 
  syntax:80 "μ " surf surf : surf 
  syntax:80 "ν " surf surf : surf 

  --term
  syntax:30 "_" : surf
  syntax:30 "()" : surf
  -- syntax:30 "y[" surf:90 "]": surf
  -- syntax:30 "x[" surf:90 "]" : surf
  syntax:30 surf:100 ";" surf:30 : surf
  syntax:30 surf:100 ":=" surf:30 : surf
  syntax:30 "(" surf "," surf ")" : surf
  syntax:30 "σ" surf : surf
  syntax:20 "for" surf:30 ":" surf "=>" surf:20 : surf 
  syntax:20 "for" surf:30 "=>" surf:20 : surf 
  syntax:20 "λ" surf:30 ":" surf "=>" surf:20 : surf 
  syntax:20 "λ" surf:30 "=>" surf:20 : surf 
  syntax:30 "λ" surf : surf 
  syntax:30 surf:30 "/" surf:100 : surf 
  syntax:30 "(" surf:30 surf:30 ")" : surf 
  syntax:30 "let" surf ":" surf:30 "=" surf:30 "=>" surf:30 : surf 
  syntax:30 "let" surf "=" surf:30 "=>" surf:30 : surf 
  syntax:30 "fix " surf:30 : surf 

  syntax:50 surf:50 "⊆" surf:51 : surf

  syntax "(" surf ")" : surf

  syntax "⟨" term "⟩" : surf 

  syntax "[: " surf ":]" : term

  macro_rules
  -- terminals
  | `([: $n:num :]) => `($n)
  | `([: $a:ident:]) => `(Ty.var $(Lean.quote (toString a.getId)))
  -- context 
  | `([: [ $x:surf ] :]) => `([ match [: $x :] with | .var name => name | _ => "" ])
  | `([: [ $x,$xs:surf,* ] :]) => `([: [ $x ] :] ++ [: [$xs,*] :])
  -- Ty 
  | `([: @ :]) => `(Ty.unit)
  | `([: ⊥ :]) => `(Ty.bot)
  | `([: ⊤ :]) => `(Ty.top)
  | `([: $a * $b:surf :]) => `(Ty.tag [: $a :] [: $b :])
  | `([: $a : $b:surf :]) => `(Ty.field [: $a :] [: $b :])
  | `([: $a -> $b :]) => `(Ty.case [: $a :] [: $b :])
  | `([: $a ∨ $b :]) => `(Ty.union [: $a :] [: $b :])
  | `([: $a + $b :]) => `(Ty.union (Ty.tag "inl" [: $a :]) (Ty.tag "inr" [: $b :]))
  | `([: $a ∧ $b :]) => `(Ty.inter [: $a :] [: $b :])
  | `([: $a × $b :]) => `(Ty.inter (Ty.field "l" [: $a :]) (Ty.field "r" [: $b :]))
  | `([: ∀ $a:surf $d:surf | $b ≤ $c :]) => `(Ty.univ [: $a :] [: $b :] [: $c :] [: $d :])
  | `([: ∀ $a:surf $b:surf :]) => `(Ty.univ [: $a :] [: @ :] [: @ :] [: $b :] )
  | `([: ∃ $a $d | $b ≤ $c  :]) => `(Ty.exis [: $a :] [: $b :] [: $c :] [: $d :])
  | `([: ∃ $a:surf $b:surf :]) => `(Ty.exis [: $a :] [: @ :] [: @ :] [: $b :] )
  | `([: μ $name $a :]) => `(Ty.recur [: $name :] [: $a :])
  | `([: ν $name $a :]) => `(Ty.corec [: $name :] [: $a :])
  --Tm
  | `([: _ :]) => `(Tm.hole)
  | `([: () :]) => `(Tm.unit)
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

  --generic
  | `([: ($a:surf) :]) => `([: $a :])

  --escape 
  | `([: ⟨ $e ⟩ :]) => pure e


  #check [: (x) :]
  #check [: [x] :]
  #eval [: ∀ [thing] thing ∨ @ | thing ≤ @ :]

  -------------------


end Surface