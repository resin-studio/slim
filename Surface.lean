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
  | var : String -> Tm 
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
  | .var id => id
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
  syntax:30 surf:30 "." surf:100 : surf 
  syntax:30 "(" surf:30 surf:30 ")" : surf 
  syntax:30 "let" surf ":" surf:30 "=" surf:30 "=>" surf:30 : surf 
  syntax:30 "let" surf "=" surf:30 "=>" surf:30 : surf 
  syntax:30 "fix " surf:30 : surf 

  syntax:50 surf:50 "⊆" surf:51 : surf

  syntax "(" surf ")" : surf

  syntax "⟨" term "⟩" : surf 

  syntax "[surf: " surf "]" : term

  macro_rules
  -- terminals
  | `([surf: $n:num ]) => `($n)
  | `([surf: $a:ident]) => `(Ty.var $(Lean.quote (toString a.getId)))
  -- context 
  | `([surf: [ $x:surf ] ]) => `([ match [surf: $x ] with | .var name => name | _ => "" ])
  | `([surf: [ $x,$xs:surf,* ] ]) => `([surf: [ $x ] ] ++ [surf: [$xs,*] ])
  -- Ty 
  | `([surf: @ ]) => `(Ty.unit)
  | `([surf: ⊥ ]) => `(Ty.bot)
  | `([surf: ⊤ ]) => `(Ty.top)
  | `([surf: $a * $b:surf ]) => `(Ty.tag [surf: $a ] [surf: $b ])
  | `([surf: $a : $b:surf ]) => `(Ty.field [surf: $a ] [surf: $b ])
  | `([surf: $a -> $b ]) => `(Ty.case [surf: $a ] [surf: $b ])
  | `([surf: $a ∨ $b ]) => `(Ty.union [surf: $a ] [surf: $b ])
  | `([surf: $a + $b ]) => `(Ty.union (Ty.tag "inl" [surf: $a ]) (Ty.tag "inr" [surf: $b ]))
  | `([surf: $a ∧ $b ]) => `(Ty.inter [surf: $a ] [surf: $b ])
  | `([surf: $a × $b ]) => `(Ty.inter (Ty.field "l" [surf: $a ]) (Ty.field "r" [surf: $b ]))
  | `([surf: ∀ $a:surf $d:surf | $b ≤ $c ]) => `(Ty.univ [surf: $a ] [surf: $b ] [surf: $c ] [surf: $d ])
  | `([surf: ∀ $a:surf $b:surf ]) => `(Ty.univ [surf: $a ] [surf: @ ] [surf: @ ] [surf: $b ] )
  | `([surf: ∃ $a $d | $b ≤ $c  ]) => `(Ty.exis [surf: $a ] [surf: $b ] [surf: $c ] [surf: $d ])
  | `([surf: ∃ $a:surf $b:surf ]) => `(Ty.exis [surf: $a ] [surf: @ ] [surf: @ ] [surf: $b ] )
  | `([surf: μ $name $a ]) => `(Ty.recur [surf: $name ] [surf: $a ])
  | `([surf: ν $name $a ]) => `(Ty.corec [surf: $name ] [surf: $a ])
  --Tm
  | `([surf: _ ]) => `(Tm.hole)
  | `([surf: () ]) => `(Tm.unit)
  | `([surf: $a ; $b ]) => `(Tm.tag [surf: $a ] [surf: $b ])
  | `([surf: $a := $b ]) => `(([surf: $a ], [surf: $b ]))
  | `([surf: for $b => $d ]) => `(([surf: $b ], [surf: $d ]))
  | `([surf: σ $a ]) => `(Tm.record [surf: $a ])
  | `([surf: ( $a , $b ) ]) => `(Tm.record [("l", [surf: $a ]), ("r", [surf:$b ])])
  | `([surf: λ $b => $d ]) => `(Tm.func [([surf: $b ], [surf: $d ])])
  | `([surf: λ $a ]) => `(Tm.func [surf: $a ])
  | `([surf: $a . $b ]) => `(Tm.proj [surf: $a ] [surf: $b ])
  | `([surf: ($a $b) ]) => `(Tm.app [surf: $a ] [surf: $b ])
  | `([surf: let $name : $a = $b => $c ]) => `(Tm.letb [surf: $name ] (Option.some [surf: $a ]) [surf: $b ] [surf: $c ])
  | `([surf: let $name = $b => $c ]) => `(Tm.letb [surf: $name ] Option.none [surf: $b ] [surf: $c ])
  | `([surf: fix $a ]) => `(Tm.fix [surf: $a ])

  --generic
  | `([surf: ($a:surf) ]) => `([surf: $a ])

  --escape 
  | `([surf: ⟨ $e ⟩ ]) => pure e


  #check [surf: (x) ]
  #check [surf: [x] ]
  #eval [surf: ∀ [thing] thing ∨ @ | thing ≤ @ ]

  -------------------


end Surface