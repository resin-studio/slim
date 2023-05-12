import Std.Data.BinomialHeap
import Init.Data.Hashable
import Lean.Data.PersistentHashMap

import Util 
import Nameless

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
  deriving Repr, Inhabited, Hashable, BEq
  #check List.repr


  def to_set [BEq α] [Hashable α] (xs : List α) : PHashMap α Unit :=
    PHashMap.from_list (xs.map fun x => (x, Unit.unit))

  def to_list [BEq α] [Hashable α] (xs : PHashMap α Unit) : List α :=
    xs.toList.map fun (x, _) => x

  namespace Ty

    def Ty.infer_abstraction (exclude : PHashMap String Unit) : Ty -> PHashMap String Unit 
    | .id name => 
      if exclude.contains name then
        {}
      else
        PHashMap.from_list [(name, Unit.unit)]
    | .unit => {} 
    | .top => {} 
    | .bot => {} 
    | .tag l ty =>
      Ty.infer_abstraction exclude ty 
    | .field l ty => 
      Ty.infer_abstraction exclude ty 
    | .union ty1 ty2 => 
      let n1 := Ty.infer_abstraction exclude ty1 
      let n2 := Ty.infer_abstraction exclude ty2
      n1 ; n2 
    | .inter ty1 ty2 => 
      let n1 := Ty.infer_abstraction exclude ty1 
      let n2 := Ty.infer_abstraction exclude ty2
      n1 ; n2 
    | .case ty1 ty2 =>
      let n1 := Ty.infer_abstraction exclude ty1 
      let n2 := Ty.infer_abstraction exclude ty2
      n1 ; n2 
    | exis n ty_c1 ty_c2 ty_pl =>
      let exclude' := exclude ; (to_set n)  
      let n_c1 := Ty.infer_abstraction exclude' ty_c1 
      let n_c2 := Ty.infer_abstraction exclude' ty_c2
      let n_pl := Ty.infer_abstraction exclude' ty_pl  
      n_c1 ; n_c2 ; n_pl
    | univ n ty_c1 ty_c2 ty_pl =>
      let exclude' := exclude ; (to_set n)  
      let n_c1 := Ty.infer_abstraction exclude' ty_c1 
      let n_c2 := Ty.infer_abstraction exclude' ty_c2
      let n_pl := Ty.infer_abstraction exclude' ty_pl  
      n_c1 ; n_c2 ; n_pl
    | recur name content =>
      Ty.infer_abstraction (exclude ; to_set [name]) content 

    protected partial def repr (ty : Ty) (n : Nat) : Format :=
    match ty with
    | .id name => name 
    | .unit => "unit" 
    | .bot => "⊥" 
    | .top => "⊤" 
    | .tag l ty1 => 
      (l ++ "@" ++ (Ty.repr ty1 n))
    | .field l ty1 => 
      Format.bracket "(" (l ++ " : " ++ (Ty.repr ty1 n)) ")"

    | .union ty1 ty2 =>
      let _ : ToFormat Ty := ⟨fun ty' => Ty.repr ty' n ⟩
      let tys := [ty1, ty2] 
      Format.bracket "("
        (Format.joinSep tys (" |" ++ Format.line))
      ")"

    | .inter (Ty.field "l" l) (Ty.field "r" r) =>
      Format.bracket "(" ((Ty.repr l n) ++ " * " ++ (Ty.repr r n)) ")"
    | .inter ty1 ty2 =>
      Format.bracket "(" ((Ty.repr ty1 n) ++ " & " ++ (Ty.repr ty2 n)) ")"
    | .case ty1 ty2 =>
      Format.bracket "(" ((Ty.repr ty1 n) ++ " ->" ++ Format.line ++ (Ty.repr ty2 n)) ")"
    | .univ names ty_c1 ty_c2 ty_pl =>
      let names_format := Format.bracket "[" (Format.joinSep names ", ") "]"
      if (ty_c1, ty_c2) == (Ty.unit, Ty.unit) then
        Format.bracket "(" (
          "forall " ++ names_format ++ " " ++ (Ty.repr ty_pl n)
        ) ")"
      else
        Format.bracket "(" (
          "forall " ++ names_format ++ " " ++ (Ty.repr ty_c1 n) ++ " <: " ++ (Ty.repr ty_c2 n) ++
            " have " ++ (Ty.repr ty_pl n)
        ) ")"
    | .exis names ty_c1 ty_c2 ty_pl =>
      let names_format := Format.bracket "[" (Format.joinSep names ", ") "]"
      if (ty_c1, ty_c2) == (Ty.unit, Ty.unit) then
        Format.bracket "{" (
          names_format ++ " " ++ 
          Ty.repr ty_pl n) "}"
      else
        Format.bracket "{" (
          names_format ++ " " ++ 
          (Ty.repr ty_pl n) ++ " with " ++
          (Ty.repr ty_c1 n) ++ " <: " ++ (Ty.repr ty_c2 n)
        ) "}"
    | .recur name ty1 =>
      Format.bracket "(" (
        "induct " ++ "[" ++ name ++ "] " ++ (Ty.repr ty1 n)
      ) ")"

    instance : Repr Ty where
      reprPrec := Ty.repr


    declare_syntax_cat surftype
    syntax "(" surftype ")" : surftype
    syntax "⟨" term "⟩" : surftype 
    syntax:100 num : surftype 
    syntax:100 ident : surftype
    syntax "[" ident,+ "]" : surftype 
    -- type
    syntax:90 "unit" : surftype
    syntax:90 "⊥" : surftype
    syntax:90 "⊤" : surftype
    syntax:90 surftype:100 "@" surftype:90 : surftype
    syntax:90 surftype:100 ":" surftype:90 : surftype
    syntax:50 surftype:51 "->" surftype:50 : surftype
    syntax:60 surftype:61 "|" surftype:60 : surftype
    syntax:70 surftype:71 "&" surftype:70 : surftype
    syntax:70 surftype:71 "*" surftype:70 : surftype

    syntax "{" surftype surftype:41 "with" surftype:41 "<:" surftype:41 "}": surftype 
    syntax "{" surftype surftype:41 "}" : surftype 

    syntax "{" surftype:41 "with" surftype:41 "<:" surftype:41 "}": surftype 
    syntax "{" surftype:41 "}" : surftype 


    syntax "forall" surftype surftype:41 "<:" surftype:41 "have" surftype:41 : surftype 
    syntax "forall" surftype surftype:41 : surftype 

    syntax "forall" surftype:41 "<:" surftype:41 "have" surftype:41 : surftype 
    syntax "forall" surftype:41 : surftype 


    syntax:40 "induct" "[" ident "]" surftype : surftype 


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
    | `([surftype: [ $x:ident ] ]) => `([ $(Lean.quote (toString x.getId)) ])
    | `([surftype: [ $x,$xs:ident,* ] ]) => `([surftype: [ $x ] ] ++ [surftype: [$xs,*] ])
    -- Ty 
    | `([surftype: unit ]) => `(Ty.unit)
    | `([surftype: ⊥ ]) => `(Ty.bot)
    | `([surftype: ⊤ ]) => `(Ty.top)
    | `([surftype: $a @ $b:surftype ]) => `(Ty.tag (idname [surftype: $a ]) [surftype: $b ])
    | `([surftype: $a : $b:surftype ]) => `(Ty.field (idname [surftype: $a ]) [surftype: $b ])
    | `([surftype: $a -> $b ]) => `(Ty.case [surftype: $a ] [surftype: $b ])
    | `([surftype: $a | $b ]) => `(Ty.union [surftype: $a ] [surftype: $b ])
    | `([surftype: $a & $b ]) => `(Ty.inter [surftype: $a ] [surftype: $b ])
    | `([surftype: $a * $b ]) => `(Ty.inter (Ty.field "l" [surftype: $a ]) (Ty.field "r" [surftype: $b ]))

    | `([surftype: { $n $d with $b <: $c }  ]) => `(Ty.exis [surftype: $n ] [surftype: $b ] [surftype: $c ] [surftype: $d ])
    | `([surftype: { $n $b:surftype } ]) => `(Ty.exis [surftype: $n ] Ty.unit Ty.unit [surftype: $b ] )

    | `([surftype: { $d with $b <: $c }  ]) => 
      `(Ty.exis (to_list (Ty.infer_abstraction {} [surftype: $d ])) [surftype: $b ] [surftype: $c ] [surftype: $d ])
    | `([surftype: { $b:surftype } ]) => 
      `(Ty.exis (to_list (Ty.infer_abstraction {} [surftype: $b ])) Ty.unit Ty.unit [surftype: $b ] )

    | `([surftype: forall $b <: $c have $d  ]) => 
      `(Ty.univ (to_list (Ty.infer_abstraction {} [surftype: $d ])) [surftype: $b ] [surftype: $c ] [surftype: $d ])
    | `([surftype: forall $b:surftype  ]) => 
      `(Ty.univ (to_list (Ty.infer_abstraction {} [surftype: $b ])) Ty.unit Ty.unit [surftype: $b ] )

    | `([surftype: forall $n $b <: $c have $d ]) => `(Ty.univ [surftype: $n ] [surftype: $b ] [surftype: $c ] [surftype: $d ])
    | `([surftype: forall $n $b:surftype ]) => `(Ty.univ [surftype: $n ] Ty.unit Ty.unit [surftype: $b ] )

    | `([surftype: induct [ $name ] $a ]) => `(Ty.recur $(Lean.quote (toString name.getId)) [surftype: $a ])

    #check [surftype: (x) ]
    #check [surftype: [x] ]
    #eval Ty.infer_abstraction {} [surftype: thing ]
    #eval [surftype: {thing | unit with thing <: unit }]


    #eval [surftype: forall bob -> {thing | unit with thing <: bob }]
    #eval [surftype: forall thing -> {thing | bob | unit with thing <: unit }]
    -- #eval [normam: forall β[0] -> {β[1] ∨ β[0] ∨ unit | β[1] <: unit }]

    #eval [surftype: {[thing, or] thing | unit with thing <: unit }]
    #eval [surftype: {thing | unit with thing <: unit }]
    -- #eval Ty.infer_abstraction 0 [surftype: $d ]) [surftype: $b ] [surftype: $c ] [surftype: $d ]
    #eval [surftype: succ*x ]
    #eval [surftype: 
        (zero@unit * nil@unit) |
        {succ@nat * cons@list with nat * list <: nat_list}
    ]

    #eval [surftype: 
      induct [nat_list] (
        (zero@unit * nil@unit) | 
        {succ@nat * cons@list with nat * list <: nat_list}
      )
    ]


    -- #eval [surftype: 
    --   nat -> (list | nat × list ≤ nat_list) 
    -- ]
    -- TODO: simplify language by using implication to encode universal and greatest fixedpoint.  
    /-
    nat_list @ (
      (zero*unit × nil*unit) ∨ 
      (succ*nat × cons*list | nat × list ≤ nat_list)
    )
    -/
    -- ∀ X . X -> (∃ Y . Y | X × Y ≤ T)
    -- ∀ X . X -> (∃ Y . Y | X × Y ≤ T)
    -- n -> (l | n × l ≤ nat_list)

    partial def pattern_abstraction : Ty -> Option (List String)
    | .id name => some [name]
    | .unit => some [] 
    | .bot => some [] 
    | .tag _ content => do 
      let names <- pattern_abstraction content
      some names
    | .field _ content => do 
      let names <- pattern_abstraction content
      some names
    | union ty1 ty2 => do
      let names1 <- pattern_abstraction ty1 
      let names2 <- pattern_abstraction ty2
      some (names1 ++ names2) 
    | .inter ty1 ty2 => do
      let names1 <- pattern_abstraction ty1 
      let names2 <- pattern_abstraction ty2
      some (names1 ++ names2) 
    | .case ty1 ty2 => do
      let names1 <- pattern_abstraction ty1 
      let names2 <- pattern_abstraction ty2
      some (names1 ++ names2) 
    | _ => none

    def normalize (bound_vars : List String) : Ty -> Option (List (List String) × Nameless.Ty)
    | id name => do
      let pos <- (List.index (fun bv => bv == name) bound_vars)
      some ([], .bvar pos)
    | .unit => some ([], .unit)
    | .bot => some ([], .bot)
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
    | .exis names ty1 ty2 ty3 => do
      let (stack1, ty1') <- (normalize (names ++ bound_vars) ty1) 
      let (stack2, ty2') <- (normalize (names ++ bound_vars) ty2) 
      let (stack3, ty3') <- (normalize (names ++ bound_vars) ty3) 
      some (names :: stack1 ++ stack2 ++ stack3, .exis names.length ty1' ty2' ty3')
    | .univ names ty1 ty2 ty3 => do
      let (stack1, ty1') <- (normalize (names ++ bound_vars) ty1) 
      let (stack2, ty2') <- (normalize (names ++ bound_vars) ty2) 
      let (stack3, ty3') <- (normalize (names ++ bound_vars) ty3) 
      some (names :: stack1 ++ stack2 ++ stack3, .univ names.length ty1' ty2' ty3')
    | .recur name ty => do
      let (stack, ty') <- (normalize (name :: bound_vars) ty) 
      some ([name] :: stack, .recur ty')


    def denormalize (names : List String) (stack : List (List String)) : Nameless.Ty ->  Option Surface.Ty
    | .bvar index =>  
      if h : names.length > index then
        let name := names.get ⟨index, h⟩
        some (.id name)
      else
        none
    | .fvar index => some (.id s!"_α_{index}")
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
    | .recur ty =>
      match stack with
      | names' :: stack'  =>
        match names' with
        | .cons name [] => do
          let ty' <- (denormalize (name :: names) stack' ty)   
          some (.recur name ty') 
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
        "#" ++ l ++ " = " ++ Tm.repr t1 n ⟩
      Format.bracket "(" (Format.joinSep fds (Format.line)) ")"
    | func fs =>
      let _ : ToFormat (Tm × Tm) := ⟨fun (pat, tb) =>
        "\\ " ++ (Tm.repr pat n) ++ " => " ++ (Tm.repr tb (n))
      ⟩
      Format.bracket "(" (Format.joinSep fs (Format.line)) ")"
    | .proj t1 l =>
      Tm.repr t1 n ++ "." ++ l
    | .app t1 t2 =>
      Format.bracket "(" (Tm.repr t1 n) ") " ++ "(" ++ Tm.repr t2 n ++ ")"
    | .letb name op_ty1 t1 t2 =>
      match op_ty1 with
      | some ty1 =>
        "let " ++ name ++ " : " ++ (Ty.repr ty1 n) ++ " = " ++  (Tm.repr t1 n) ++ " in" ++
        Format.line  ++ (Tm.repr t2 n) 
      | none =>
        "let " ++ name ++ " = " ++  (Tm.repr t1 n) ++ " in" ++
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
    syntax:30 "(" surfterm "," surfterm ")" : surfterm

    -- syntax:20 surfterm:30 "=>" surfterm:20 : surfterm 
    -- syntax:20 "λ" surfterm:30 "=>" surfterm:20 : surfterm 
    -- syntax:30 "λ" surfterm : surfterm 

    syntax:30 "#" ident "=" surfterm:30 : surfterm
    syntax:30 "#" ident "=" surfterm:30 surfterm: surfterm

    syntax:20 "\\" surfterm:30 "=>" surfterm:20 : surfterm
    syntax:20 "\\" surfterm:30 "=>" surfterm:20 surfterm: surfterm

    syntax:30 surfterm:30 "." surfterm:100 : surfterm 
    syntax:30 "(" surfterm:30 surfterm:30 ")" : surfterm 
    syntax:30 "let" ident ":" surfterm:30 "=" surfterm:30 "in" surfterm:30 : surfterm 
    syntax:30 "let" ident "=" surfterm:30 "in" surfterm:30 : surfterm 
    syntax:30 "fix " surfterm:30 : surfterm 

    syntax "[surfterm: " surfterm "]" : term

    def idname v := match v with 
    | (Tm.id x) => x 
    | _ => ""

    def record_fields : Tm -> List (String × Tm)
    | record fields => fields
    | _ =>  []

    def function_cases : Tm -> List (Tm × Tm)
    | func cases => cases 
    | _ =>  []


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
    | `([surfterm: ( $a , $b ) ]) => `(Tm.record [("l", [surfterm: $a ]), ("r", [surfterm:$b ])])

    | `([surfterm: # $a = $b ]) => `( Tm.record [ ($(Lean.quote (toString a.getId)), [surfterm: $b ]) ]  )
    | `([surfterm: # $a = $b $xs ]) => `( Tm.record (($(Lean.quote (toString a.getId)), [surfterm: $b ]) :: (Tm.record_fields [surfterm: $xs ])))

    | `([surfterm: \ $b => $d ]) => `(Tm.func [([surfterm: $b ], [surfterm: $d ])])
    | `([surfterm: \ $b => $d $xs ]) => `( Tm.func (([surfterm: $b ], [surfterm: $d ]) :: (Tm.function_cases [surfterm: $xs ])))

    | `([surfterm: $a . $b ]) => `(Tm.proj [surfterm: $a ] [surfterm: $b ])
    | `([surfterm: ($a $b) ]) => `(Tm.app [surfterm: $a ] [surfterm: $b ])
    | `([surfterm: let $name : $a = $b in $c ]) => `(Tm.letb $(Lean.quote (toString name.getId)) (Option.some [surfterm: $a ]) [surfterm: $b ] [surfterm: $c ])
    | `([surfterm: let $name = $b in $c ]) => `(Tm.letb $(Lean.quote (toString name.getId)) Option.none [surfterm: $b ] [surfterm: $c ])
    | `([surfterm: fix $a ]) => `(Tm.fix [surfterm: $a ])


    #eval [surfterm:
        ⟨Tm.id "succ"⟩;x
    ]

    #eval [surfterm:
        succ;x
    ]

    #eval [surfterm:
      fix(\ self => (
        \ (succ;x, succ;y) => (self (x, y))
        \ (zero;(), y) => y
        \ (x, zero;()) => x 
      ))
    ]

    #eval [surfterm:
      \ x => x
    ]

    #eval [surfterm:
      \ x => ⟨Tm.id "x"⟩
    ]
    end Tm

    structure Abstraction where 
      names : List String
      type_map : PHashMap String (List (List String))

    partial def pattern_abstraction : Tm -> Option (List String)
    | .hole => some []
    | .unit => some []
    | .id name => some [name]
    | .tag _ content => do
      let names <- pattern_abstraction content
      some names
    | .record fields => do 
      List.foldr (fun (_, content) result => do
        let result_names <- result
        let names <- pattern_abstraction content
        if List.any names (List.contains result_names) then
          none
        else
          some (names ++ result_names) 
      ) none fields
    | _ => none



    partial def normalize (bound_vars : List String) : Tm -> Option (List Abstraction × Nameless.Tm)
    | .hole => some ([], .hole) 
    | .unit => some ([], .unit)
    | .id name => do
      let idx <- bound_vars.index fun bv => name == bv 
      some ([], .bvar idx) 
    | .tag label content => do
      let (stack', content') <- normalize bound_vars content
      some (stack', .tag label content')
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
        let pattern_names <- pattern_abstraction pattern
        let (stack', pattern') <- normalize (pattern_names ++ bound_vars) pattern 
        let (stack'', content') <- normalize (pattern_names ++ bound_vars) content
        let absstraction : Abstraction := ⟨pattern_names, {}⟩ 
        some (absstraction :: stack' ++ stack'' ++ result_stack, (pattern', content') :: result_cases) 
      ) none cases
      some (result_stack, .func result_cases)
    | .proj record label => do
      let (stack', record') <- normalize bound_vars record 
      some (stack', .proj record' label)
    | .app f arg => do
      let (stack', f') <- normalize bound_vars f 
      let (stack'', arg') <- normalize bound_vars arg 
      .some (stack' ++ stack'', .app f' arg')
    | .letb name ty_op arg body =>
      let names_ty_op' := (do
        let ty <- ty_op 
        Ty.normalize [] ty
      )
      let ty_op' := (do 
        let (_, ty') <- names_ty_op'
        some ty'
      )
      let ty_map := (match names_ty_op' with
      | some (ty_stack', _) => PHashMap.from_list [(name, ty_stack')]
      | none => {}
      )
      let abstraction : Abstraction := ⟨[name], ty_map⟩
      do
      let (stack', arg') <- normalize bound_vars arg 
      let (stack'', body') <- normalize (name :: bound_vars) body 
      some (abstraction :: stack' ++ stack'', .letb ty_op' arg' body')
    | .fix content => do
      let (stack', content') <- normalize bound_vars content
      some (stack', .fix content')

    partial def denormalize (abstraction : Abstraction) (stack : List Abstraction) : Nameless.Tm ->  Option Surface.Tm
    | .hole => some .hole 
    | .unit => some .unit 
    | .bvar idx =>
      let names := abstraction.names
      if h : names.length > idx then
        let name := names.get ⟨idx, h⟩
        some (.id name)
      else
        none
    | .fvar index => some (.id s!"_x_{index}")
    | .tag label content => do
      let content' <- denormalize abstraction stack content
      some (.tag label content')
    | .record fields => do
      let fields' <- List.foldr (fun (label, content) result => do
        let fields' <- result
        let content' <- denormalize abstraction stack content 
        some ((label, content') :: fields')
      ) none fields
      some (.record fields')
    | .func cases => do 
      let cases' <- List.foldr (fun (pattern, body) result => do
        let cases' <- result
        let pattern' <- denormalize abstraction (abstraction :: stack) pattern 
        let body' <- denormalize abstraction (abstraction :: stack) body 
        some ((pattern', body') :: cases')
      ) none cases
      some (.func cases')
    | .proj record label => do
      let record' <- denormalize abstraction stack record 
      some (.proj record' label)
    | .app f arg => do 
      let f' ← denormalize abstraction stack f 
      let arg' ← denormalize abstraction stack arg
      some (.app f' arg') 
    | .letb ty_op arg body => 
      match abstraction.names with
      | [name] => 
        let ty_op' := (do
          let ty <- ty_op
          let ty_stack <- abstraction.type_map.find? name
          let ty' <- Ty.denormalize [] ty_stack ty 
          some ty' 
        )
        do
        let arg' ← denormalize abstraction stack arg
        let body' ← denormalize abstraction stack body
        some (.letb name ty_op' arg' body') 
      | _ => none
    | .fix content => do
      let content' <- denormalize abstraction stack content 
      some (.fix content')



--------------------------------------

  def nat_list := [surftype: 
    induct [nat_list] (
      (zero@unit * nil@unit) | 
      {succ@nat * cons@list with nat * list <: nat_list}
    )
  ]
  #eval nat_list

  def nat_to_list := [surftype:
    forall nat -> {list with nat * list <: nat_list}
  ] 

  #eval nat_to_list

  #eval  [surfterm:
    fix(\ self => ( 
      \ (succ;x, succ;y) => (self (x, y))
      \ (zero;(), y) => y
      \ (x zero;()) => x 
    )) 
  ]

  
  #eval  [surfterm:
    let f = fix(\ self => ( 
      \ (succ;x, succ;y) => (self (x, y))
      \ (zero;(), y) => y
      \ (x zero;()) => x 
    )) in 
    (f (succ;succ;zero;(), succ;zero;()))
  ]

  ----------------------------------
  #eval [surfterm: #x = hello;() #y = world;()]
  --------------------------------------

end Surface