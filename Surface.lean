import Std.Data.BinomialHeap
import Init.Data.Hashable
import Lean.Data.PersistentHashMap

import Util 
import Normal

open Lean PersistentHashMap

open Std

namespace Surface

  inductive Ty : Type
  | id : String -> Ty
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

  namespace Ty

    protected partial def repr (ty : Ty) (n : Nat) : Format :=
    match ty with
    | .id name => name 
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


    declare_syntax_cat surftype
    syntax "(" surftype ")" : surftype
    syntax "⟨" term "⟩" : surftype 
    syntax:100 num : surftype 
    syntax:100 ident : surftype
    syntax "[" surftype,+ "]" : surftype 
    -- type
    syntax:90 "@" : surftype
    syntax:90 "⊥" : surftype
    syntax:90 "⊤" : surftype
    syntax:90 surftype:100 "*" surftype:90 : surftype
    syntax:90 surftype:100 ":" surftype:90 : surftype
    syntax:50 surftype:51 "->" surftype:50 : surftype
    syntax:60 surftype:61 "∨" surftype:60 : surftype
    syntax:60 surftype:61 "+" surftype:60 : surftype
    syntax:70 surftype:71 "∧" surftype:70 : surftype
    syntax:70 surftype:71 "×" surftype:70 : surftype
    syntax:40 "∃" surftype surftype:40 "|" surftype "≤" surftype: surftype 
    syntax:40 "∃" surftype surftype:40 : surftype 
    syntax:40 "∀" surftype surftype:40 "|" surftype "≤" surftype : surftype 
    syntax:40 "∀" surftype surftype:40 : surftype 
    syntax:80 "μ " surftype surftype : surftype 
    syntax:80 "ν " surftype surftype : surftype 


    syntax "[surftype: " surftype "]" : term

    def idname v := match v with 
    | (Ty.id x) => x 
    | _ => ""

    macro_rules
    --generic
    | `([surftype: ($a:surftype) ]) => `([surftype: $a ])
    --escape 
    | `([surftype: ⟨ $e ⟩ ]) => pure e
    -- terminals
    | `([surftype: $n:num ]) => `($n)
    | `([surftype: $a:ident]) => `(Ty.id $(Lean.quote (toString a.getId)))
    -- context 
    | `([surftype: [ $x:surftype ] ]) => `([ [surftype: $x ] ])
    | `([surftype: [ $x,$xs:surftype,* ] ]) => `([surftype: [ $x ] ] ++ [surftype: [$xs,*] ])
    -- Ty 
    | `([surftype: @ ]) => `(Ty.unit)
    | `([surftype: ⊥ ]) => `(Ty.bot)
    | `([surftype: ⊤ ]) => `(Ty.top)
    | `([surftype: $a * $b:surftype ]) => `(Ty.tag (idname [surftype: $a ]) [surftype: $b ])
    | `([surftype: $a : $b:surftype ]) => `(Ty.field (idname [surftype: $a ]) [surftype: $b ])
    | `([surftype: $a -> $b ]) => `(Ty.case [surftype: $a ] [surftype: $b ])
    | `([surftype: $a ∨ $b ]) => `(Ty.union [surftype: $a ] [surftype: $b ])
    | `([surftype: $a + $b ]) => `(Ty.union (Ty.tag "inl" [surftype: $a ]) (Ty.tag "inr" [surftype: $b ]))
    | `([surftype: $a ∧ $b ]) => `(Ty.inter [surftype: $a ] [surftype: $b ])
    | `([surftype: $a × $b ]) => `(Ty.inter (Ty.field "l" [surftype: $a ]) (Ty.field "r" [surftype: $b ]))
    | `([surftype: ∀ $a:surftype $d:surftype | $b ≤ $c ]) => `(Ty.univ 
        (List.map (fun | Ty.id name => name | _ => "") [surftype: $a ]) 
        [surftype: $b ] [surftype: $c ] [surftype: $d ])
    | `([surftype: ∀ $a:surftype $b:surftype ]) => `(Ty.univ 
          (List.map (fun | Ty.id name => name | _ => "") [surftype: $a ]) 
          [surftype: @ ] [surftype: @ ] [surftype: $b ] )
    | `([surftype: ∃ $a $d | $b ≤ $c  ]) => `(Ty.exis 
          (List.map (fun | Ty.id name => name | _ => "") [surftype: $a ]) 
          [surftype: $b ] [surftype: $c ] [surftype: $d ])
    | `([surftype: ∃ $a:surftype $b:surftype ]) => `(Ty.exis 
          (List.map (fun | Ty.id name => name | _ => "") [surftype: $a ]) 
          [surftype: @ ] [surftype: @ ] [surftype: $b ] )
    | `([surftype: μ $name $a ]) => `(Ty.recur [surftype: $name ] [surftype: $a ])
    | `([surftype: ν $name $a ]) => `(Ty.corec [surftype: $name ] [surftype: $a ])

    #check [surftype: (x) ]
    #check [surftype: [x] ]
    #eval [surftype: ∀ [thing] thing ∨ @ | thing ≤ @ ]
    #eval [surftype: succ*x ]

    def normalize (bound_vars : List String) : Ty -> Option (List (List String) × Normal.Ty)
    | id name => do
      let pos <- (List.index (fun bv => bv == name) bound_vars)
      some ([], .bvar pos)
    | .unit => some ([], .unit)
    | .bot => some ([], .unit)
    | .top => some ([], .top)
    | .tag name content => do 
      let (stack, content') <- normalize bound_vars content
      some (stack, .tag name content')
    | .field name content => do
      let (stack, content') <- normalize bound_vars content
      some (stack, .field name content')
    | .union ty1 ty2 => do 
      let (stack1, ty1') <- (normalize bound_vars ty1) 
      let (stack2, ty2') <- (normalize bound_vars ty2) 
      some (stack1 ++ stack2, .union ty1' ty2')
    | .inter ty1 ty2 => do
      let (stack1, ty1') <- (normalize bound_vars ty1) 
      let (stack2, ty2') <- (normalize bound_vars ty2) 
      some (stack1 ++ stack2, .inter ty1' ty2')
    | .case ty1 ty2 => do 
      let (stack1, ty1') <- (normalize bound_vars ty1) 
      let (stack2, ty2') <- (normalize bound_vars ty2) 
      some (stack1 ++ stack2, .case ty1' ty2')
    | .univ names ty1 ty2 ty3 => do
      let (stack1, ty1') <- (normalize (names ++ bound_vars) ty1) 
      let (stack2, ty2') <- (normalize (names ++ bound_vars) ty2) 
      let (stack3, ty3') <- (normalize (names ++ bound_vars) ty3) 
      some (names :: stack1 ++ stack2 ++ stack3, .univ names.length ty1' ty2' ty3')
    | .exis names ty1 ty2 ty3 => do
      let (stack1, ty1') <- (normalize (names ++ bound_vars) ty1) 
      let (stack2, ty2') <- (normalize (names ++ bound_vars) ty2) 
      let (stack3, ty3') <- (normalize (names ++ bound_vars) ty3) 
      some (names :: stack1 ++ stack2 ++ stack3, .exis names.length ty1' ty2' ty3')
    | .recur name ty => do
      let (stack, ty') <- (normalize (name :: bound_vars) ty) 
      some ([name] :: stack, .recur ty')
    | .corec name ty => do
      let (stack, ty') <- (normalize (name :: bound_vars) ty)
      some ([name] :: stack, .corec ty')


    def denormalize (names : List String) (stack : List (List String)) : Normal.Ty ->  Option Surface.Ty
    | .bvar index =>  
      if h : names.length > index then
        let name := names.get ⟨index, h⟩
        some (.id name)
      else
        none
    | .fvar index => some (.id s!"_x_{index}")
    | .unit => some .unit 
    | .bot => some .bot 
    | .top => some .top 
    | .tag label content => do
      let content' <- (denormalize names stack content)   
      some (.tag label content') 
    | .field label content => do
      let content' <- (denormalize names stack content)   
      some (.field label content') 
    | .union ty1 ty2 => do
      let ty1' <- (denormalize names stack ty1)   
      let ty2' <- (denormalize names stack ty2)   
      some (.union ty1' ty2') 
    | .inter ty1 ty2 => do
      let ty1' <- (denormalize names stack ty1)   
      let ty2' <- (denormalize names stack ty2)   
      some (.inter ty1' ty2') 
    | .case ty1 ty2 => do
      let ty1' <- (denormalize names stack ty1)   
      let ty2' <- (denormalize names stack ty2)   
      some (.case ty1' ty2') 
    | .univ n ty1 ty2 ty3 => 
      match stack with
      | names' :: stack'  =>
        if names'.length == n then do
          let ty1' <- (denormalize (names' ++ names) stack' ty1)   
          let ty2' <- (denormalize (names' ++ names) stack' ty2)   
          let ty3' <- (denormalize (names' ++ names) stack' ty3)   
          some (.univ names' ty1' ty2' ty3') 
        else
          none
      | [] => none
    | .exis n ty1 ty2 ty3 => 
      match stack with
      | names' :: stack'  =>
        if names'.length == n then do
          let ty1' <- (denormalize (names' ++ names) stack' ty1)   
          let ty2' <- (denormalize (names' ++ names) stack' ty2)   
          let ty3' <- (denormalize (names' ++ names) stack' ty3)   
          some (.exis names' ty1' ty2' ty3') 
        else
          none
      | [] => none
    | .recur ty =>
      match stack with
      | names' :: stack'  =>
        match names' with
        | .cons name [] => do
          let ty' <- (denormalize (name :: names) stack' ty)   
          some (.recur name ty') 
        | _ => none
      | [] => none
    | .corec ty =>
      match stack with
      | names' :: stack'  =>
        match names' with
        | .cons name [] => do
          let ty' <- (denormalize (name :: names) stack' ty)
          some (.corec name ty') 
        | _ => none
      | [] => none

  end Ty

  ------------------------------------------------------------------------------------------

  inductive Tm : Type
  | hole : Tm 
  | unit : Tm
  | id : String -> Tm 
  | tag : String -> Tm -> Tm
  | record : List (String × Tm) -> Tm
  | func : List (Tm × Tm) -> Tm
  | proj : Tm -> String -> Tm
  | app : Tm -> Tm -> Tm
  | letb : String -> Option Ty -> Tm -> Tm -> Tm
  | fix : Tm -> Tm
  deriving Repr, Inhabited, BEq

  namespace Tm

    protected partial def repr (t : Tm) (n : Nat) : Format :=
    match t with
    | .hole => 
      "_"
    | .unit =>
      "()"
    | .id name => name 
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




    declare_syntax_cat surfterm
    syntax "(" surfterm ")" : surfterm
    syntax "⟨" term "⟩" : surfterm 
    syntax:100 num : surfterm 
    syntax:100 ident : surfterm
    syntax "[" surfterm,+ "]" : surfterm 
    --term
    syntax:30 "_" : surfterm
    syntax:30 "()" : surfterm
    syntax:30 surfterm:100 ";" surfterm:30 : surfterm
    syntax:30 surfterm:100 ":=" surfterm:30 : surfterm
    syntax:30 "(" surfterm "," surfterm ")" : surfterm
    syntax:30 "σ" surfterm : surfterm
    syntax:20 surfterm:30 "=>" surfterm:20 : surfterm 
    syntax:20 "λ" surfterm:30 "=>" surfterm:20 : surfterm 
    syntax:30 "λ" surfterm : surfterm 
    syntax:30 surfterm:30 "." surfterm:100 : surfterm 
    syntax:30 "(" surfterm:30 surfterm:30 ")" : surfterm 
    syntax:30 "let" surfterm ":" surfterm:30 "=" surfterm:30 "=>" surfterm:30 : surfterm 
    syntax:30 "let" surfterm "=" surfterm:30 "=>" surfterm:30 : surfterm 
    syntax:30 "fix " surfterm:30 : surfterm 

    syntax "[surfterm: " surfterm "]" : term

    def idname v := match v with 
    | (Tm.id x) => x 
    | _ => ""

    macro_rules
    --generic
    | `([surfterm: ($a:surfterm) ]) => `([surfterm: $a ])
    --escape 
    | `([surfterm: ⟨ $e ⟩ ]) => pure e
    -- terminals
    | `([surfterm: $n:num ]) => `($n)
    | `([surfterm: $a:ident]) => `(Tm.id $(Lean.quote (toString a.getId)))
    -- context 
    | `([surfterm: [ $x:surfterm ] ]) => `([ [surfterm: $x ] ])
    | `([surfterm: [ $x,$xs:surfterm,* ] ]) => `([surfterm: [ $x ] ] ++ [surfterm: [$xs,*] ])
    --Tm
    | `([surfterm: _ ]) => `(Tm.hole)
    | `([surfterm: () ]) => `(Tm.unit)
    | `([surfterm: $a ; $b ]) => `(Tm.tag (idname [surfterm: $a ]) [surfterm: $b ])
    | `([surfterm: $a := $b ]) => `((idname [surfterm: $a ], [surfterm: $b ]))
    | `([surfterm: $b => $d ]) => `(([surfterm: $b ], [surfterm: $d ]))
    | `([surfterm: σ $a ]) => `(Tm.record [surfterm: $a ])
    | `([surfterm: ( $a , $b ) ]) => `(Tm.record [("l", [surfterm: $a ]), ("r", [surfterm:$b ])])
    | `([surfterm: λ $b => $d ]) => `(Tm.func [([surfterm: $b ], [surfterm: $d ])])
    | `([surfterm: λ $a ]) => `(Tm.func [surfterm: $a ])
    | `([surfterm: $a . $b ]) => `(Tm.proj [surfterm: $a ] [surfterm: $b ])
    | `([surfterm: ($a $b) ]) => `(Tm.app [surfterm: $a ] [surfterm: $b ])
    | `([surfterm: let $name : $a = $b => $c ]) => `(Tm.letb [surfterm: $name ] (Option.some [surfterm: $a ]) [surfterm: $b ] [surfterm: $c ])
    | `([surfterm: let $name = $b => $c ]) => `(Tm.letb [surfterm: $name ] Option.none [surfterm: $b ] [surfterm: $c ])
    | `([surfterm: fix $a ]) => `(Tm.fix [surfterm: $a ])


    #eval [surfterm:
        ⟨Tm.id "succ"⟩;x
    ]

    #eval [surfterm:
        succ;x
    ]

    #eval [surfterm:
      fix(λ self => λ[
        (succ;x, succ;y) => (self (x, y)),
        (zero;(), y) => y,
        (x, zero;()) => x 
      ])
    ]

    #eval [surfterm:
      λ [x => x]
    ]

    #eval [surfterm:
      λ [x => ⟨Tm.id "x"⟩]
    ]
    end Tm

    structure Bindings where 
      intros : List String
      type_map : PHashMap String (List (List String) × Normal.Tm)

    partial def pattern_bindings : Tm -> Option (List String)
    | .hole => some []
    | .unit => some []
    | .id name => some [name]
    | .tag _ content => do
      let names <- pattern_bindings content
      some names
    | .record fields => do 
      List.foldr (fun (_, content) result => do
        let result_names <- result
        let names <- pattern_bindings content
        if List.any names (List.contains result_names) then
          none
        else
          some (names ++ result_names) 
      ) none fields
    | _ => none

    partial def normalize (bound_vars : List String) : Tm -> Option (List Bindings × Normal.Tm)
    | .hole => some ([], .hole) 
    | .unit => some ([], .unit)
    | .id name => do
      let idx <- bound_vars.index fun bv => name == bv 
      some ([], .bvar idx) 
    | .tag label content => do
      let (stack, content') <- normalize bound_vars content
      some (stack, .tag label content')
    | .record fields => do 
      let (result_stack, result_fields) <- List.foldr (fun (label, content) result => do
        let (result_stack, result_fields) <- result
        let (stack', content') <- normalize bound_vars content
        some (stack' ++ result_stack, (label, content') :: result_fields) 
      ) none fields
      some (result_stack, .record result_fields)
    | .func cases => do 
      let (result_stack, result_cases) <- List.foldr (fun (pattern, content) result => do
        let (result_stack, result_cases) <- result
        let pattern_names <- pattern_bindings pattern
        let (stack', pattern') <- normalize (pattern_names ++ bound_vars) pattern 
        let (stack'', content') <- normalize (pattern_names ++ bound_vars) content
        let bindings : Bindings := ⟨pattern_names, {}⟩ 
        some (bindings :: stack' ++ stack'' ++ result_stack, (pattern', content') :: result_cases) 
      ) none cases
      some (result_stack, .func result_cases)
    -- TODO
    -- | .proj : Tm -> String -> Tm
    -- | .app : Tm -> Tm -> Tm
    -- | .letb : String -> Option Ty -> Tm -> Tm -> Tm
    -- | .fix : Tm -> Tm
    | _ => none


end Surface