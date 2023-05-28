import Std.Data.BinomialHeap
import Init.Data.Hashable
import Lean.Data.PersistentHashMap
import Lean.Data.PersistentHashSet

import Util 
import Nameless

open Lean PersistentHashMap PersistentHashSet
open PHashSet

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
  | univ : String -> Option Ty -> Ty -> Ty
  | exis : List String -> Ty -> Ty -> Ty -> Ty
  | recur : String -> Ty -> Ty
  deriving Repr, Inhabited, Hashable, BEq
  #check List.repr


  namespace Ty

    partial def infer_abstraction (exclude : PHashSet String) : Ty -> PHashSet String 
    | .id name => 
      if exclude.contains name then
        {}
      else
        from_list [name]
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
      n1 + n2 
    | .inter ty1 ty2 => 
      let n1 := Ty.infer_abstraction exclude ty1 
      let n2 := Ty.infer_abstraction exclude ty2
      n1 + n2 
    | .case ty1 ty2 =>
      let n1 := Ty.infer_abstraction exclude ty1 
      let n2 := Ty.infer_abstraction exclude ty2
      n1 + n2 
    | exis n ty_c1 ty_c2 ty_pl =>
      let exclude' := exclude + (from_list n)  
      let n_c1 := Ty.infer_abstraction exclude' ty_c1 
      let n_c2 := Ty.infer_abstraction exclude' ty_c2
      let n_pl := Ty.infer_abstraction exclude' ty_pl  
      n_c1 + n_c2 + n_pl
    | univ name op_ty_c ty_pl =>
      let exclude := exclude.insert name  
      let n_c := match Option.map (infer_abstraction exclude) op_ty_c with
      | some n_c => n_c 
      | none => {} 

      let n_pl := Ty.infer_abstraction exclude ty_pl  
      n_c + n_pl
    | recur name content =>
      Ty.infer_abstraction (exclude + from_list [name]) content 

    def intersect : Ty -> Ty -> Ty
    | .top, ty => ty
    | ty, .top => ty
    | ty1, ty2 => inter ty1 ty2

    def intersect_over (f : (Ty × Ty) -> Ty) (constraints : List (Ty × Ty)) : Ty :=
      (constraints.foldr (fun (lhs, rhs) ty_acc =>
        Ty.intersect (f (lhs, rhs)) ty_acc 
      ) Ty.top)

    protected partial def repr (ty : Ty) (n : Nat) : Format :=
    match ty with
    | .id name => name 
    | .unit => "unit" 
    | .bot => "⊥" 
    | .top => "⊤" 
    | .tag l ty1 => 
      ("?" ++ l ++ " " ++ (Ty.repr ty1 n))
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
    | .univ name op_ty_c ty_pl =>
      match op_ty_c with
      | none =>
        Format.bracket "(" (
          name ++ " >> " ++ (Ty.repr ty_pl n)
        ) ")"
      | some ty_c  =>
        Format.bracket "(" (
          "(" ++ name ++  " <: " ++ (Ty.repr ty_c n) ++ ") >> " ++ (Ty.repr ty_pl n)
        ) ")"
    | .exis names ty_c1 ty_c2 ty_pl =>
      let names_format := (Format.joinSep names ", ") ++ " // "
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
    syntax:90 "?" surftype:100 surftype:90 : surftype
    syntax:90 surftype:100 ":" surftype:90 : surftype
    syntax:50 surftype:51 "->" surftype:50 : surftype
    syntax:60 surftype:61 "|" surftype:60 : surftype
    syntax:70 surftype:71 "&" surftype:70 : surftype
    syntax:70 surftype:71 "*" surftype:70 : surftype


    syntax "{" surftype surftype:41 "with" surftype "}": surftype 
    syntax "{" surftype surftype:41 "}" : surftype 

    syntax "{" surftype:41 "with" surftype "}": surftype 
    syntax "{" surftype:41 "}" : surftype 


    syntax:50  ident ">>" surftype:50: surftype 
    syntax:50  "(" ident "<:" surftype:51 ")" ">>" surftype:50 : surftype 

    syntax:50 "induct" "[" ident "]" surftype : surftype 

    -- constraints
    syntax:40 surftype:41 "<:" surftype:41 : surftype
    syntax:40 surftype:41 "<:" surftype:41 "," surftype: surftype
    ------------


    syntax "[surftype| " surftype "]" : term

    def idname v := match v with 
    | (Ty.id x) => x 
    | _ => ""

    macro_rules
    --generic
    | `([surftype| ($a:surftype) ]) => `([surftype| $a ])
    --escape 
    | `([surftype| ⟨ $e ⟩ ]) => pure e
    -- terminals
    | `([surftype| $n:num ]) => `($n)
    | `([surftype| $a:ident]) => `(Ty.id $(Lean.quote (toString a.getId)))
    -- context 
    | `([surftype| [ $x:ident ] ]) => `([ $(Lean.quote (toString x.getId)) ])
    | `([surftype| [ $x,$xs:ident,* ] ]) => `([surftype| [ $x ] ] ++ [surftype| [$xs,*] ])
    -- Ty 
    | `([surftype| unit ]) => `(Ty.unit)
    | `([surftype| ⊥ ]) => `(Ty.bot)
    | `([surftype| ⊤ ]) => `(Ty.top)
    | `([surftype| ? $a $b:surftype ]) => `(Ty.tag (idname [surftype| $a ]) [surftype| $b ])
    | `([surftype| $a : $b:surftype ]) => `(Ty.field (idname [surftype| $a ]) [surftype| $b ])
    | `([surftype| $a -> $b ]) => `(Ty.case [surftype| $a ] [surftype| $b ])
    | `([surftype| $a | $b ]) => `(Ty.union [surftype| $a ] [surftype| $b ])
    | `([surftype| $a & $b ]) => `(Ty.inter [surftype| $a ] [surftype| $b ])
    | `([surftype| $a * $b ]) => `(Ty.inter (Ty.field "l" [surftype| $a ]) (Ty.field "r" [surftype| $b ]))

    -- constraints
    | `([surftype| $b <: $c  ]) => `([([surftype| $b ],[surftype| $c ])])
    | `([surftype| $b <: $c , $xs ]) => `(([surftype| $b ],[surftype| $c ]) :: [surftype| $xs])
    --------------

    | `([surftype| { $n $d with $xs }  ]) => `(intersect_over
        (fun (lhs, rhs) => Ty.exis [surftype| $n ] lhs rhs  [surftype| $d ])
        [surftype| $xs ]
      )
    | `([surftype| { $n $b:surftype } ]) => `(Ty.exis [surftype| $n ] Ty.unit Ty.unit [surftype| $b ] )

    | `([surftype| { $d with $xs }  ]) => `(intersect_over
        (fun (lhs, rhs) => Ty.exis (toList (Ty.infer_abstraction {} [surftype| $d ])) lhs rhs [surftype| $d ])
        [surftype| $xs ]
      )

    | `([surftype| { $b:surftype } ]) => 
      `(Ty.exis (toList (Ty.infer_abstraction {} [surftype| $b ])) Ty.unit Ty.unit [surftype| $b ] )

    | `([surftype| $i:ident >> $d  ]) => 
      `(Ty.univ $(Lean.quote (toString i.getId)) none [surftype| $d ])

    | `([surftype| ( $i:ident <: $c ) >> $d  ]) => 
      `(Ty.univ $(Lean.quote (toString i.getId)) (some [surftype| $c ]) [surftype| $d ])

    | `([surftype| induct [ $name ] $a ]) => `(Ty.recur $(Lean.quote (toString name.getId)) [surftype| $a ])
    
------------------------------------------------------------

    #eval [surftype| {X} ]
    #eval [surftype| {X with X <: ?ooga unit, X <: ?booga unit} ]
    #eval [surftype| {X with X <: ?ooga unit} ]

    #eval [surftype| {[X] X with (X * Y) <: ?booga unit} ] 
    #eval [surftype| {[X] X with X * Y <: ?booga unit} ] 
    #eval [surftype| (X <: ?ooga unit) >> X -> ?booga unit ] 
    #eval [surftype| (X <: ?ooga unit) >>  X -> {[Y] Y with X * Y <: ?booga unit} ] 

------------------------------------------------------------

    #check [surftype| (x) ]
    #check [surftype| [x] ]
    #eval infer_abstraction {} [surftype| thing ]
    #eval [surftype| {thing | unit with thing <: unit }]


    #eval [surftype| bob >> bob -> {thing | unit with thing <: bob }]
    #eval [surftype| thing >> thing -> {thing | bob | unit with thing <: unit }]

    #eval [surftype| {[thing, or] thing | unit with thing <: unit }]
    #eval [surftype| {thing | unit with thing <: unit }]
    -- #eval Ty.infer_abstraction 0 [surftype| $d ]) [surftype| $b ] [surftype| $c ] [surftype| $d ]
    #eval [surftype| succ*x ]
    #eval [surftype| 
        (?zero unit * ?nil unit) |
        {?succ nat * ?cons list with nat * list <: nat_list}
    ]

    #eval [surftype| 
      induct [nat_list] (
        (?zero unit * ?nil unit) | 
        {?succ nat * ?cons list with nat * list <: nat_list}
      )
    ]


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

    partial def to_nameless (free_vars : List String) (bound_vars : List String) : Ty -> Option (List (List String) × Nameless.Ty)
    | id name => do
      match (List.index (fun bv => bv == name) bound_vars) with
      | some pos => some ([], .bvar pos)
      | none => do
        let pos <- (List.index (fun fv => fv == name) free_vars)
        some ([], .fvar pos)
    | .unit => some ([], .unit)
    | .bot => some ([], .bot)
    | .top => some ([], .top)
    | .tag name content => do 
      let (stack, content') <- to_nameless free_vars bound_vars content
      some (stack, .tag name content')
    | .field name content => do
      let (stack, content') <- to_nameless free_vars bound_vars content
      some (stack, .field name content')
    | .union ty1 ty2 => do 
      let (stack1, ty1') <- (to_nameless free_vars bound_vars ty1) 
      let (stack2, ty2') <- (to_nameless free_vars bound_vars ty2) 
      some (stack1 ++ stack2, .union ty1' ty2')
    | .inter ty1 ty2 => do
      let (stack1, ty1') <- (to_nameless free_vars bound_vars ty1) 
      let (stack2, ty2') <- (to_nameless free_vars bound_vars ty2) 
      some (stack1 ++ stack2, .inter ty1' ty2')
    | .case ty1 ty2 => do 
      let (stack1, ty1') <- (to_nameless free_vars bound_vars ty1) 
      let (stack2, ty2') <- (to_nameless free_vars bound_vars ty2) 
      some (stack1 ++ stack2, .case ty1' ty2')
    | .exis names ty1 ty2 ty3 => do
      let (stack1, ty1') <- (to_nameless free_vars (names ++ bound_vars) ty1) 
      let (stack2, ty2') <- (to_nameless free_vars (names ++ bound_vars) ty2) 
      let (stack3, ty3') <- (to_nameless free_vars (names ++ bound_vars) ty3) 
      some (names :: stack1 ++ stack2 ++ stack3, .exis names.length ty1' ty2' ty3')
    | .univ name op_ty_c ty3 => do
      let op <- (Option.map (to_nameless free_vars (name :: bound_vars)) op_ty_c)
      let (stack1, op_ty_c') := (match op with
      | .some (stack1, ty_c') => (stack1, some ty_c')
      | .none => ([], none)
      )
      let (stack3, ty3') <- (to_nameless free_vars (name :: bound_vars) ty3) 
      some ([name] :: stack1 ++ stack3, .univ op_ty_c' ty3')
    | .recur name ty => do
      let (stack, ty') <- (to_nameless free_vars (name :: bound_vars) ty) 
      some ([name] :: stack, .recur ty')

    def extract_free_vars : Ty -> PHashSet String
    | id name => from_list [name] 
    | .unit => {} 
    | bot => {} 
    | top => {} 
    | tag _ content => 
      extract_free_vars content
    | field _ content => 
      extract_free_vars content
    | union ty1 ty2  => 
      extract_free_vars ty1 + extract_free_vars ty2 
    | inter ty1 ty2  =>
      extract_free_vars ty1 + extract_free_vars ty2 
    | case ty1 ty2  =>
      extract_free_vars ty1 + extract_free_vars ty2 
    | exis bound_names tyc1 tyc2 ty_pl =>
      let names := (extract_free_vars tyc1) + (extract_free_vars tyc2) + (extract_free_vars ty_pl)
      from_list ((toList names).filter (fun n => !(bound_names.contains n)))
    | univ bound_name op_tyc ty_pl =>
      let names := (match op_tyc with
      | some tyc => (extract_free_vars tyc)
      | none => {} 
      ) + (extract_free_vars ty_pl)
      from_list ((toList names).filter (fun n => n != bound_name))
    | recur bound_name ty =>
      let names := (extract_free_vars ty)
      from_list ((toList names).filter (fun n => n != bound_name))


    partial def from_nameless (free_names : List String) (names : List String) (stack : List (List String)) : 
      Nameless.Ty ->  Option (List (List String) × Surface.Ty)
    | .bvar index =>  
      if names_proof : names.length > index then
        let name := names.get ⟨index, names_proof⟩
        some (stack, .id name)
      else if free_names_proof : free_names.length > index then
        let free_name := free_names.get ⟨index, free_names_proof⟩
        some (stack, .id free_name)
      else
        none
    | .fvar index => 
      if h : index < free_names.length then  
        some (stack, .id (free_names.get ⟨index, h⟩))
      else
        some (stack, .id (s!"α_{index}_")) 
    | .unit => some (stack, .unit)
    | .bot => some (stack, .bot)
    | .top => some (stack, .top)
    | .tag label content => do
      let (stack, content') <- (from_nameless free_names names stack content)   
      some (stack, .tag label content') 
    | .field label content => do
      let (stack, content') <- (from_nameless free_names names stack content)   
      some (stack, .field label content') 
    | .union ty1 ty2 => do
      let (stack, ty1') <- (from_nameless free_names names stack ty1)   
      let (stack, ty2') <- (from_nameless free_names names stack ty2)   
      some (stack, .union ty1' ty2') 
    | .inter ty1 ty2 => do
      let (stack, ty1') <- (from_nameless free_names names stack ty1)   
      let (stack, ty2') <- (from_nameless free_names names stack ty2)   
      some (stack, .inter ty1' ty2') 
    | .case ty1 ty2 => do
      let (stack, ty1') <- (from_nameless free_names names stack ty1)   
      let (stack, ty2') <- (from_nameless free_names names stack ty2)   
      some (stack, .case ty1' ty2') 
    | .exis n ty1 ty2 ty3 => 
      match stack with
      | names' :: stack'  =>
        if names'.length == n then do
          let (stack', ty1') <- (from_nameless free_names (names' ++ names) stack' ty1)   
          let (stack', ty2') <- (from_nameless free_names (names' ++ names) stack' ty2)   
          let (stack', ty3') <- (from_nameless free_names (names' ++ names) stack' ty3)   
          some (stack', .exis names' ty1' ty2' ty3') 
        else
          none
      | [] => none
    | .univ op_tyc ty3 => 
      match stack with
      | names' :: stack'  =>
        match names' with
        | [name] => do
          let op <- Option.map (from_nameless free_names (name :: names) stack') op_tyc   
          let (stack', op_tyc') := (match op with
          | some (stack', tyc') => (stack', some tyc')
          | none => (stack', none) 
          )
          let (stack', ty3') <- (from_nameless free_names (name :: names) stack' ty3)   
          some (stack', .univ name op_tyc' ty3') 
        | _ => none
      | [] => none
    | .recur ty =>
      match stack with
      | names' :: stack'  =>
        match names' with
        | [name] => do
          let (stack', ty') <- (from_nameless free_names (name :: names) stack' ty)   
          some (stack', .recur name ty') 
        | _ => none
      | [] => none

    def extract_bound_stack (i : Nat): Nameless.Ty -> Nat × List (List String)  
    | .bvar _ => (i, []) 
    | .fvar _ => (i, []) 
    | .unit => (i, []) 
    | .bot => (i, []) 
    | .top => (i, []) 
    | .tag _ content => 
      extract_bound_stack i content 
    | .field _ content => 
      extract_bound_stack i content 
    | .union ty1 ty2  => 
      let (i, stack1) := extract_bound_stack i ty1 
      let (i, stack2) := extract_bound_stack i ty2 
      (i, stack1 ++ stack2)
    | .inter ty1 ty2  =>
      let (i, stack1) := extract_bound_stack i ty1 
      let (i, stack2) := extract_bound_stack i ty2 
      (i, stack1 ++ stack2)
    | .case ty1 ty2  =>
      let (i, stack1) := extract_bound_stack i ty1 
      let (i, stack2) := extract_bound_stack i ty2 
      (i, stack1 ++ stack2)
    | .univ op_tyc ty_pl =>
      let (i, stack_c) := match op_tyc with
      | some tyc => extract_bound_stack i tyc
      | none => (i, [])
      let (i, stack_pl) := extract_bound_stack i ty_pl
      let (i, names) := (i + 1, [s!"T{i}"])
      (i, names :: stack_c ++ stack_pl)
    | .exis n tyc1 tyc2 ty_pl =>
      let (i, stack1) := extract_bound_stack i tyc1 
      let (i, stack2) := extract_bound_stack i tyc2 
      let (i, stack_pl) := extract_bound_stack i ty_pl
      let (i, names) := (i + n, (List.range n).map (fun j => s!"T{i + j}"))
      (i, names :: stack1 ++ stack2 ++ stack_pl)
    | .recur ty =>
      let (i, stack) := extract_bound_stack i ty 
      let (i, names) := (i + 1, [s!"T{i}"])
      (i, names :: stack)

    partial def unify_reduce (ty1 ty2 ty_result : Surface.Ty) : Option Surface.Ty := do
      let free_vars := toList (extract_free_vars [surftype| ⟨ty1⟩ * ⟨ty2⟩])
      let (_, ty1') <- to_nameless free_vars [] ty1
      let (_, ty2') <- to_nameless free_vars [] ty2
      let (_, ty_result') <- to_nameless free_vars [] ty_result
      let nameless_ty := Nameless.Ty.unify_reduce free_vars.length ty1' ty2' ty_result' 
      let (_, bound_stack) := extract_bound_stack 0 nameless_ty
      let (_, ty_surf) <- Surface.Ty.from_nameless free_vars [] bound_stack nameless_ty 
      ty_surf

    -- partial def unify_reduce (ty1 ty2 ty_result : Surface.Ty) : Option Nameless.Ty := do
    --   let free_vars := to_list (extract_free_vars [surftype| ⟨ty1⟩ * ⟨ty2⟩])
    --   let (stack1, ty1') <- to_nameless free_vars [] ty1
    --   let (stack2, ty2') <- to_nameless free_vars [] ty2
    --   let (stack_result, ty_result') <- to_nameless free_vars [] ty_result
    --   let nameless_ty := Nameless.Ty.unify_reduce free_vars.length ty1' ty2' ty_result' 
    --   nameless_ty

    -------------------------------------------------
    def nat_ := [surftype|
      induct [self] ?zero unit | ?succ self
    ]

    #eval nat_

    #eval extract_free_vars [surftype| (?succ ?succ ?succ something) * (?zero unit | ?succ ⟨nat_⟩) ] 
    def fvs := extract_free_vars [surftype| (?succ ?succ ?succ something) * (?zero unit | ?succ ⟨nat_⟩) ] 
    
    #eval to_nameless (toList fvs) [] [surftype| (?succ something) ] 
    

    def result_pair := to_nameless [] [] nat_
    #eval result_pair
    #eval match result_pair with 
      | some (stack, ty) => from_nameless [] [] stack ty 
      | none => none 

    #eval unify_reduce
    [surftype| (?succ ?succ ?succ something) ] 
    [surftype| ?zero unit | ?succ ⟨nat_⟩ ] 
    [surftype| something ]

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
      "#" ++ l ++ " " ++ (Tm.repr t1 n)
    | record [("l", l), ("r", r)] =>
      let _ : ToFormat Tm := ⟨fun t1 => Tm.repr t1 n ⟩
      Format.bracket "(" (Format.joinSep [l, r] ("," ++ Format.line)) ")"
    | record fds =>
      let _ : ToFormat (String × Tm) := ⟨fun (l, t1) =>
        "@" ++ l ++ " = " ++ Tm.repr t1 n ⟩
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
    syntax:90 num : surfterm 
    syntax:90 ident : surfterm

    syntax:90 "(" surfterm ")" : surfterm
    syntax:90 "⟨" term "⟩" : surfterm 
    syntax:90 "_" : surfterm
    syntax:90 "()" : surfterm
    syntax:90 "(" surfterm "," surfterm ")" : surfterm
    syntax:90 "(" surfterm:80 surfterm:80 ")" : surfterm 

    syntax:80 "#" surfterm:90 surfterm:80 : surfterm
    syntax:80 surfterm:90 "." surfterm:80 : surfterm 

    syntax:75 surfterm:75 "|>" surfterm:76 : surfterm 


    syntax:70 "@" ident "=" surfterm:71 : surfterm
    syntax:70 "@" ident "=" surfterm:71 surfterm:70: surfterm

    syntax:70 "\\" surfterm:71 "=>" surfterm:70 : surfterm
    syntax:70 "\\" surfterm:71 "=>" surfterm:70 surfterm:70: surfterm

    syntax:70 "if" surfterm:71 "then" surfterm:71 "else" surfterm:70: surfterm

    syntax:70 "let" ident ":" surftype "=" surfterm:70 "in" surfterm:70 : surfterm 
    syntax:70 "let" ident "=" surfterm:70 "in" surfterm:70 : surfterm 
    syntax:70 "fix " surfterm:70 : surfterm 

    syntax "[surfterm| " surfterm "]" : term

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
    | `([surfterm| ($a:surfterm) ]) => `([surfterm| $a ])
    --escape 
    | `([surfterm| ⟨ $e ⟩ ]) => pure e
    -- terminals
    | `([surfterm| $n:num ]) => `($n)
    | `([surfterm| $a:ident]) => `(Tm.id $(Lean.quote (toString a.getId)))
    --Tm
    | `([surfterm| _ ]) => `(Tm.hole)
    | `([surfterm| () ]) => `(Tm.unit)
    | `([surfterm| #$a $b ]) => `(Tm.tag (idname [surfterm| $a ]) [surfterm| $b ])
    | `([surfterm| ( $a , $b ) ]) => `(Tm.record [("l", [surfterm| $a ]), ("r", [surfterm|$b ])])

    | `([surfterm| @ $a = $b ]) => `( Tm.record [ ($(Lean.quote (toString a.getId)), [surfterm| $b ]) ]  )
    | `([surfterm| @ $a = $b $xs ]) => `( Tm.record (($(Lean.quote (toString a.getId)), [surfterm| $b ]) :: (Tm.record_fields [surfterm| $xs ])))

    | `([surfterm| \ $b => $d ]) => `(Tm.func [([surfterm| $b ], [surfterm| $d ])])
    | `([surfterm| \ $b => $d $xs ]) => `( Tm.func (([surfterm| $b ], [surfterm| $d ]) :: (Tm.function_cases [surfterm| $xs ])))


    | `([surfterm| if $test then $t else $f ]) => `( 
      [surfterm| 
        ($test) |> (
          \ #⟨Tm.id "true"⟩ () => ($t)
          \ #⟨Tm.id "false"⟩ () => ($f)
        )
      ]
    )

    | `([surfterm| $a . $b ]) => `(Tm.proj [surfterm| $a ] [surfterm| $b ])
    | `([surfterm| ($a $b) ]) => `(Tm.app [surfterm| $a ] [surfterm| $b ])
    | `([surfterm| $b |> $a ]) => `(Tm.app [surfterm| $a ] [surfterm| $b ])
    | `([surfterm| let $name : $a = $b in $c ]) => `(Tm.letb $(Lean.quote (toString name.getId)) (Option.some [surftype| $a ]) [surfterm| $b ] [surfterm| $c ])
    | `([surfterm| let $name = $b in $c ]) => `(Tm.letb $(Lean.quote (toString name.getId)) Option.none [surfterm| $b ] [surfterm| $c ])
    | `([surfterm| fix $a ]) => `(Tm.fix [surfterm| $a ])


    #eval [surfterm|
        #⟨Tm.id "succ"⟩ x
    ]

    #eval [surfterm|
        #succ x
    ]

    #eval [surfterm|
      fix(\ self => (
        \ (#succ x, #succ y) => (self (x, y))
        \ (#zero (), y) => y
        \ (x, #zero ()) => x 
      ))
    ]

    #eval [surfterm|
      \ x => x
    ]

    #eval [surfterm|
      \ x => ⟨Tm.id "x"⟩
    ]

    #eval [surfterm|
      #true () |> (
        \ #true () => #hello ()
        \ #false () => #world ()
      )
    ]

    #eval [surfterm|
      if (f ()) then
        #hello ()
      else
        #world ()
    ]

    #eval [surfterm|
      if (f ()) then
        #hello ()
      else if (g ()) then
        #middle ()
      else
        #world ()
    ]
    #eval [surfterm|
      if (f ()) then
        #hello ()
      else (if (g ()) then
        #middle ()
      else
        #world ())
    ]


    structure Abstraction where 
      names : List String
      map_type : PHashMap String (List (List String))

    def Abstraction.concat (abs1 abs2 : Abstraction) : Abstraction :=
      ⟨abs1.names ++ abs2.names, abs2.map_type ; abs1.map_type⟩ 

    partial def extract_pattern_vars : Tm -> Option (List String)
    | .hole => some []
    | .unit => some []
    | .id name => some [name]
    | .tag _ content => do
      let names <- extract_pattern_vars content
      some names
    | .record fields => do 
      List.foldrM (fun (_, content) names_acc => do
        let names <- extract_pattern_vars content
        if List.any names (List.contains names_acc) then
          none
        else
          some (names ++ names_acc) 
      ) [] fields
    | _ => none



    #check List.foldrM
    partial def to_nameless (type_names : List String) (bound_vars : List String) : Tm -> Option (List Abstraction × Nameless.Tm)
    | .hole => some ([], .hole) 
    | .unit => some ([], .unit)
    | .id name => do
      let idx <- bound_vars.index fun bv => name == bv 
      some ([], .bvar idx) 
    | .tag label content => do
      let (stack', content') <- to_nameless type_names bound_vars content
      some (stack', .tag label content')
    | .record fields => do 
      let (result_stack, result_fields) <- List.foldrM (fun (label, content) (stack_acc, fields_acc) => do
        let (stack', content') <- to_nameless type_names bound_vars content
        some (stack' ++ stack_acc, (label, content') :: fields_acc) 
      ) ([], []) fields
      some (result_stack, .record result_fields)
    | .func cases => do
      let (result_stack, result_cases) <- List.foldrM (fun (pattern, content) (stack_acc, cases_acc) => do
        let pattern_names <- extract_pattern_vars pattern
        let (stack', pattern') <- to_nameless type_names (pattern_names ++ bound_vars) pattern 
        let (stack'', content') <- to_nameless type_names (pattern_names ++ bound_vars) content
        let absstraction : Abstraction := ⟨pattern_names, {}⟩ 
        some (absstraction :: stack' ++ stack'' ++ stack_acc, (pattern', content') :: cases_acc) 
      ) ([], []) cases
      some (result_stack, .func result_cases)
    | proj target label => do
      let (stack', target') <- to_nameless type_names bound_vars target 
      some (stack', .proj target' label)
    | .app f arg => do
      let (stack', f') <- to_nameless type_names bound_vars f 
      let (stack'', arg') <- to_nameless type_names bound_vars arg 
      .some (stack' ++ stack'', .app f' arg')
    | .letb name ty_op arg body =>
      let names_ty_op' := (do
        let ty <- ty_op 
        Ty.to_nameless type_names [] ty
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
      let (stack', arg') <- to_nameless type_names bound_vars arg 
      let (stack'', body') <- to_nameless type_names (name :: bound_vars) body 
      some (abstraction :: stack' ++ stack'', .letb ty_op' arg' body')
    | .fix content => do
      let (stack', content') <- to_nameless type_names bound_vars content
      some (stack', .fix content')

    partial def from_nameless (abstraction : Abstraction) (stack : List Abstraction) : 
    Nameless.Tm ->  Option (List Abstraction × Surface.Tm)
    | .hole => some (stack, .hole) 
    | .unit => some (stack, .unit) 
    | .bvar idx =>
      let names := abstraction.names
      if h : names.length > idx then
        let name := names.get ⟨idx, h⟩
        some (stack, .id name)
      else
        none
    | .fvar index => none
    | .tag label content => do
      let (stack, content') <- from_nameless abstraction stack content
      some (stack, .tag label content')
    | .record fields => do
      let (stack', fields') <- List.foldrM (fun (label, content) (stack', fields') => do
        let (stack', content') <- from_nameless abstraction stack' content 
        some (stack', (label, content') :: fields')
      ) (stack, []) fields
      some (stack', .record fields')
    | .func cases => do 
      let (stack', cases') <- List.foldrM (fun (pattern, body) (stack', cases') => do
        match stack' with
        | abstraction' :: stack' => do
          let n <- Nameless.Tm.pattern_wellformed 0 pattern
          if abstraction.names.length == n then
            let abstraction := Abstraction.concat abstraction' abstraction
            let (stack', pattern') <- from_nameless abstraction stack' pattern 
            let (stack', body') <- from_nameless abstraction stack' body 
            some (stack', (pattern', body') :: cases')
          else
            none
        | [] => none 
      ) (stack, []) cases
      some (stack', .func cases')
    | .proj target label => do
      let (stack, target') <- from_nameless abstraction stack target 
      some (stack, .proj target' label)
    | .app f arg => do 
      let (stack, f') <- from_nameless abstraction stack f 
      let (stack, arg') <- from_nameless abstraction stack arg
      some (stack, .app f' arg') 
    | .letb ty_op arg body => 
      match abstraction.names with
      | [name] => 
        let ty_op' := (do
          let ty <- ty_op
          let ty_stack <- abstraction.map_type.find? name
          let (_, ty') <- Ty.from_nameless [] [] ty_stack ty 
          some ty' 
        )
        do
        let (stack, arg') <- from_nameless abstraction stack arg
        let (stack, body') <- from_nameless abstraction stack body
        some (stack, .letb name ty_op' arg' body') 
      | _ => none
    | .fix content => do
      let (stack, content') <- from_nameless abstraction stack content 
      some (stack, .fix content')

    partial def infer_reduce (type_names : List String) (t : Surface.Tm) : Option Surface.Ty := do
      let (_, t_nl) <- to_nameless type_names [] t 
      let ty_nl := Nameless.Tm.infer_reduce (type_names.length) t_nl
      let (_, stack_nl) := Ty.extract_bound_stack 0 ty_nl
      let (_, ty_surf) <- Surface.Ty.from_nameless type_names [] stack_nl ty_nl 
      ty_surf

    -- debugging
    partial def infer_reduce_debug (type_names : List String) (t : Surface.Tm) : Option (Nameless.Ty) :=  do
      let (_, t_nl) <- to_nameless type_names [] t 
      let ty_nl := Nameless.Tm.infer_reduce (type_names.length) t_nl
      ty_nl
      -- let (_, ty_surf) <- Surface.Ty.from_nameless [] [] stack_nl ty_nl 
      -- ty_surf

    partial def infer_reduce_wt (type_names : List String) (t : Surface.Tm) (ty : Surface.Ty) : Option Surface.Ty := do
      let (_, t_nl) <- to_nameless type_names [] t 
      let (_, ty_nl) <- Ty.to_nameless type_names [] ty 
      let ty_nl := Nameless.Tm.infer_reduce_wt type_names.length t_nl ty_nl
      let (_, stack_nl) := Ty.extract_bound_stack 0 ty_nl
      let (_, ty_surf) <- Surface.Ty.from_nameless type_names [] stack_nl ty_nl 
      ty_surf

  end Tm


    --------------------------------------
  #eval Tm.infer_reduce [] [surfterm|
    #succ #zero ()

  ]

  def nat_list := [surftype| 
    induct [nat_list]
      (?zero unit * ?nil unit) | 
      {?succ nat * ?cons list with (nat * list) <: nat_list}
  ]
  #eval nat_list

  def nat_ := [surftype| 
    induct [NAT] ?zero unit | ?succ NAT
  ]

  #eval Tm.infer_reduce [] [surfterm|
    let f : (A <: ⟨nat_⟩) >> A -> {B with A * B <: ⟨nat_list⟩} = _ in 
    (f (#succ#zero()))
  ]

--------------------------------------


  def nat_to_list := [surftype|
    nat >> nat -> {list with nat * list <: nat_list}
  ] 

  #eval nat_to_list

  #eval  [surfterm|
    fix(\ self => ( 
      \ (#succ x, #succ y) => (self (x, y))
      \ (#zero(), y) => y
      \ (x, #zero()) => x 
    )) 
  ]

  #eval Tm.infer_reduce [] [surfterm|
    fix(\ self => ( 
      \ (#succ x, #succ y) => (self (x, y))
      \ (#zero(), y) => y
      \ (x, #zero()) => x 
    )) 
  ]

  
  #eval  [surfterm|
    let f = fix(\ self => ( 
      \ (#succ x, #succ y) => (self (x, y))
      \ (#zero(), y) => y
      \ (x, #zero ()) => x 
    )) in 
    (f (#succ#succ#zero(), #succ#zero()))
  ]

  #eval Tm.infer_reduce [] [surfterm|
    let f = fix(\ self => ( 
      \ (#succ x, #succ y) => (self (x, y))
      \ (#zero(), y) => y
      \ (x, #zero()) => x 
    )) in 
    (f (#succ#succ#zero(), #succ#zero()))
  ]

  #eval Tm.infer_reduce [] [surfterm|
    ((fix(\ self => ( 
      \ (#succ x, #succ y) => (self (x, y))
      \ (#zero(), y) => y
      \ (x, #zero()) => x 
    ))) (#succ#succ#zero(), #succ#zero()))
  ]


  ----------------------------------
  #eval [surfterm| @x = #hello() @y = #world()]
  --------------------------------------



  -- relational unification
  def plus := [surftype| 
    induct [plus] 
      {x : ?zero unit & y : n & z : n} | 
      {x : ?succ X & y : Y & z : ?succ Z with 
        (x : X & y : Y & z : Z) <: plus 
      }
  ]

  -- expected:
  /-
  (?zero unit * ?succ ?succ ?zero unit) |
  (?succ ?zero unit * ?succ ?zero unit) | 
  (?succ ?succ ?zero unit * ?zero unit)
  -/
  #eval Ty.unify_reduce [surftype|
    (
      x : X &
      y : Y &
      z : (?succ ?succ ?zero unit)
    )
  ] plus
  [surftype| X * Y ]

  #eval plus


  --------------- examples from liquid types paper -----------------------------
  def NAT := [surftype| 
    induct [NAT] ?zero unit | ?succ NAT
  ]

  def BOOL := [surftype| 
    ?true unit | ?false unit
  ]


  def LE := [surftype| 
    induct [LE]
      {?zero unit * ⟨NAT⟩} |
      {?succ X * ?succ Y with X * Y <: LE}
  ]

  #eval Tm.infer_reduce ["X", "Y"] [surfterm| 
    let x : X = _ in
    let y : Y = _ in
    (x, y)
  ] 

  -- TODO
  -- diverges
  -- #eval Tm.infer_reduce [] [surfterm| 
  --   let max : (forall X * Y -> {Z with (X * Z) * (Y * Z) <: ⟨LE⟩ * ⟨LE⟩}) = 
  --   (\ (x, y) => if #true() then y else x) in
  --   max
  -- ] 

  ------ debugging --------------
  -- #eval Tm.infer_reduce [] [surfterm| 
  --   -- TODO: subtyping constraint over pair is causing divergence
  --   -- TODO: try removing adjustments 
  --   -- TODO: try adding restriction that RHS is not abstract; i.e. has no type variables 
  --   let max : (forall [X, Y] X * Y -> {[Z] Z with (Z * X) <: ⟨NAT⟩ * ⟨NAT⟩}) = 
  --   (\ (x, y) => x) in
  --   max
  -- ] 
  ------------------------------- 

  -- expected: fail
  #eval Ty.unify_reduce
  [surftype| X >> Y >> X * Y -> Y ]
  [surftype| (X >> Y >> X * Y -> {Z with (X * Z) * (Y * Z) <: ⟨LE⟩ * ⟨LE⟩}) ]
  [surftype| ?hmm unit ]

  -- TODO: reproduce liquid types result saying that max(x,y) :{Z with (X * Z) : LE, (Y, Z) : LE}
  -- diverges
  -- #eval Tm.infer_reduce [] [surfterm| 
  --   let le : ⟨NAT⟩ * ⟨NAT⟩ -> ⟨BOOL⟩ = fix \ self =>
  --     \ (#zero(), y) => #true()  
  --     \ (#succ x, #succ y) => (self (x, y)) 
  --     \ (#succ x, #zero()) => #false() 
  --   in
  --   let max : (forall X * Y -> {Z with (X * Z) * (Y * Z) <: ⟨LE⟩ * ⟨LE⟩}) = 
  --   \ (x, y) => if (le (x, y)) then y else x in
  --   max
  -- ] 


  --------------------

  -- TODO: type is missing mention of ?succ and ?zero
  #eval Tm.infer_reduce [] [surfterm| 
    let le : ⟨NAT⟩ * ⟨NAT⟩ -> ⟨BOOL⟩ = fix \ self =>
      \ (#zero(), y) => #true()  
      \ (#succ x, #succ y) => (self (x, y)) 
      \ (#succ x, #zero()) => #false() 
    in
    let max = \ (x, y) => if (le (x, y)) then y else x in
    max
  ] 

  -- TODO: it is merely returning the type of the right argument
  -- expected: ?succ ?succ ?zero unit
  #eval Tm.infer_reduce [] [surfterm| 
    let le : ⟨NAT⟩ * ⟨NAT⟩ -> ⟨BOOL⟩ = fix \ self =>
      \ (#zero(), y) => #true()  
      \ (#succ x, #succ y) => (self (x, y)) 
      \ (#succ x, #zero()) => #false() 
    in
    let max = \ (x, y) => if (le (x, y)) then y else x in
    let x = (max ((#succ #succ #zero()), #zero()))  in
    x
  ] 

  -- expected: ?succ ?succ ?zero unit
  #eval Tm.infer_reduce [] [surfterm| 
    let le : ⟨NAT⟩ * ⟨NAT⟩ -> ⟨BOOL⟩ = fix \ self =>
      \ (#zero(), y) => #true()  
      \ (#succ x, #succ y) => (self (x, y)) 
      \ (#succ x, #zero()) => #false() 
    in
    let max = \ (x, y) => if (le (x, y)) then y else x in
    -- let x : {[X] X with (X * ?succ ?succ ?zero unit) <: ⟨LE⟩ } = (max (#succ #zero(), (#succ #succ #zero()))) in
    let x : ?succ ?succ ?zero unit | ?succ ?zero unit = (max (#succ #zero(), (#succ #succ #zero()))) in
    x
  ] 
  --------------------------------

  -- expected: fail 
  #eval Tm.infer_reduce [] [surfterm| 
    let le : ⟨NAT⟩ * ⟨NAT⟩ -> ⟨BOOL⟩ = fix \ self =>
      \ (#zero(), y) => #true()  
      \ (#succ x, #succ y) => (self (x, y)) 
      \ (#succ x, #zero()) => #false() 
    in
    let max = \ (x, y) => if (le (x, y)) then y else x in
    let x : {[X, Y] X with (X * ?zero unit) <: ⟨LE⟩ } = (max (#succ #zero(), (#succ #succ #zero()))) in
    x
  ] 

  -- expected: fail 
  #eval Tm.infer_reduce [] [surfterm| 
    let le = (fix \ self => (
      \ (#zero(), y) => #true()  
      \ (#succ x, #succ y) => (self (x, y)) 
      \ (#succ x, #zero()) => #false() 
    )) in
    let max = (\ (x, y) => if (le (x, y)) then y else x) in
    let x : ?succ ?zero unit = (max (#succ #zero(), (#succ #succ #zero()))) in
    x
  ] 

  -- expected: fail 
  #eval Tm.infer_reduce [] [surfterm| 
    let le = (fix \ self => (
      \ (#zero(), y) => #true()  
      \ (#succ x, #succ y) => (self (x, y)) 
      \ (#succ x, #zero()) => #false() 
    )) in
    let max = (\ (x, y) => if (le (x, y)) then y else x) in
    let x : {[X] X with (X * ?succ ?zero unit) <: ⟨LE⟩ } = (max (#succ #zero(), (#succ #succ #zero()))) in
    x
  ] 

  -- expected: fail 
  #eval Ty.unify_reduce
  [surftype| (?succ ?succ ?zero unit | ?succ ?zero unit)
  ]
  [surftype| ?succ ?zero unit ]
  [surftype| ?hmm unit ]

 
  -- expected: fail 
  #eval Ty.unify_reduce
  [surftype| ?succ ?succ ?zero unit | ?succ ?zero unit ]
  [surftype| {[X] X with (X * ?succ ?zero unit) <: ⟨LE⟩ } ]
  [surftype| ?whoops unit ]

  -- expected: ⊥
  #eval Tm.infer_reduce_wt []
  [surfterm| #succ #succ #zero () ] 
  [surftype| {[X] X with (X * ?succ ?zero unit) <: ⟨LE⟩ } ] 

  #eval Tm.infer_reduce_wt []
  [surfterm| #succ #succ #zero () ] 
  [surftype| ?succ ?zero unit ] 

  ------------------------------





  ---------- generics ----------------

  #eval Tm.infer_reduce [] [surfterm|
    ((\ #cons (x, y) => x) (#cons (#one (), #two ())))
  ]
  -- expected: ?one unit


  #eval Tm.infer_reduce [] [surfterm|
    let f = (\ #cons (x, y) => x) in 
    f  
  ]
  -- expected: (forall (?cons (T0 * T1) -> T0))

  #eval Tm.infer_reduce [] [surfterm|
    let f : X >> Y >> ?cons (X * Y) -> X = _ in
    (f (#cons (#ooga (), #booga ())))  
  ]

  ---------- path discriminatin ----------------
  #eval Tm.infer_reduce [] [surfterm|
    let f = fix(\ loop => ( 
      \ #zero () => #nil (),
      \ #succ x => #cons (loop x)
    )) in 
    (f (#succ #zero ()))
  ]
  -- expected: ?cons ?nil unit


  #eval Tm.infer_reduce [] [surfterm|
    let f : (?zero unit -> ?nil unit) & (?succ ?zero unit -> ?cons ?nil unit) = _ in 
    (f (#succ #zero ()))
  ]
  -- expected: ?cons ?nil unit

  -- expected: some ?two unit
  #eval Tm.infer_reduce [] 
  [surfterm|
  let f : (
    (X >> (?hello X -> ?world unit)) & 
    (X >> ?one X -> ?two unit)
  ) = _ in 
  (f #one ())
  ]


  ---------- adjustment ----------------

  -- inferring unions (widening)
  #eval Tm.infer_reduce [] [surfterm|
    let f : X >> X -> (X -> (X * X)) = _ in 
    ((f #hello ()) #world ())
  ]
  -- expected: ((?world unit | ?hello unit) * (?world unit | ?hello unit))

  -- inferring intersections (narrowing)
  #eval Tm.infer_reduce [] [surfterm|
  let from_uno : ?uno unit -> unit = _ in 
  let from_dos: ?dos unit -> unit = _ in 
  (\ x =>
    ((from_uno x), (from_dos x)))
  ]
  -- expected: (?uno unit & ?dos unit -> (unit * unit))
  -- reduces to: (⊥ -> (unit * unit))



end Surface