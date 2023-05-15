import Std.Data.BinomialHeap
import Init.Data.Hashable
import Lean.Data.PersistentHashMap

import Util

open Lean PersistentHashMap
open Std


partial def multi_step {T : Type} [BEq T] (step : T -> T) (source : T): T :=
  let sink := step source 
  if sink == source then
    sink
  else 
    multi_step step sink

namespace Nameless 

  inductive Dir : Type
  | up | dn
  deriving Repr, Inhabited, Hashable, BEq


  def assume_env (i_u_env_ty : Nat × List α) 
  (f : Nat -> α -> (Nat × List β)) :
  (Nat × List β) :=
    let (i, u_env_ty) := i_u_env_ty
    List.foldl (fun (i, u_acc) env_ty =>
      let (i, u_env_ty) := (f i env_ty)
      (i, u_acc ++ u_env_ty)
    ) (i, []) u_env_ty 



  inductive Ty : Type
  | bvar : Nat -> Ty  
  | fvar : Nat -> Ty
  | unit : Ty
  | top : Ty
  | bot : Ty
  | tag : String -> Ty -> Ty
  | field : String -> Ty -> Ty
  | union : Ty -> Ty -> Ty
  | inter : Ty -> Ty -> Ty
  | case : Ty -> Ty -> Ty
  | exis : Nat -> Ty -> Ty -> Ty -> Ty
  | univ : Nat -> Ty -> Ty -> Ty -> Ty
  | recur : Ty -> Ty
  deriving Repr, Inhabited, Hashable, BEq
  -- #check List.repr

  namespace Ty
    -- TODO: use Combo to construct generic traversal/type tree walker
    inductive Combo (α : Type)
    | bvar : Nat -> Combo α  
    | fvar : Nat -> Combo α
    | unit : Combo α
    | bot : Combo α
    | tag : String -> α -> Combo α
    | field : String -> α -> Combo α
    | union : α -> α -> Combo α
    | inter : α -> α -> Combo α
    | case : α -> α -> Combo α
    | exis : α -> α -> α -> Combo α
    | univ : α -> α -> α -> Combo α
    | recur : α -> Combo α
    deriving Repr, Inhabited, Hashable, BEq

    def infer_abstraction (start : Nat) : Ty -> Nat
    | .bvar idx => (idx + 1) - start
    | .fvar id => 0 
    | .unit => 0 
    | .top => 0 
    | .bot => 0 
    | .tag l ty =>
      infer_abstraction start ty 
    | .field l ty => 
      infer_abstraction start ty 
    | .union ty1 ty2 => 
      let n1 := infer_abstraction start ty1 
      let n2 := infer_abstraction start ty2
      if n1 > n2 then n1 else n2 
    | .inter ty1 ty2 => 
      let n1 := infer_abstraction start ty1 
      let n2 := infer_abstraction start ty2
      if n1 > n2 then n1 else n2 
    | .case ty1 ty2 =>
      let n1 := infer_abstraction start ty1 
      let n2 := infer_abstraction start ty2
      if n1 > n2 then n1 else n2 
    | exis n ty_c1 ty_c2 ty_pl =>
      let n_c1 := infer_abstraction (start + n) ty_c1 
      let n_c2 := infer_abstraction (start + n) ty_c2
      let n_pl := infer_abstraction (start + n) ty_pl  
      Nat.max (Nat.max n_c1 n_c2) n_pl
    | univ n ty_c1 ty_c2 ty_pl =>
      let n_c1 := infer_abstraction (start + n) ty_c1 
      let n_c2 := infer_abstraction (start + n) ty_c2
      let n_pl := infer_abstraction (start + n) ty_pl  
      Nat.max (Nat.max n_c1 n_c2) n_pl
    | recur content =>
      infer_abstraction (start + 1) content 



    declare_syntax_cat lesstype
    syntax:100 num : lesstype 
    syntax:100 ident : lesstype
    syntax:90 "β["lesstype:100"]" : lesstype
    syntax:90 "α["lesstype:100"]" : lesstype
    syntax:90 "unit" : lesstype
    syntax:90 "⊤" : lesstype
    syntax:90 "⊥" : lesstype
    syntax:90 "?" lesstype:100 lesstype:90 : lesstype
    syntax:90 lesstype:100 ":" lesstype:90 : lesstype
    syntax:50 lesstype:51 "->" lesstype:50 : lesstype
    syntax:60 lesstype:61 "|" lesstype:60 : lesstype
    syntax:70 lesstype:71 "&" lesstype:70 : lesstype
    syntax:70 lesstype:71 "*" lesstype:70 : lesstype

    syntax "{" "[" lesstype "]" lesstype:41 "with" lesstype:41 "<:" lesstype:41 "}": lesstype 
    syntax "{" "[" lesstype "]" lesstype:41 "}" : lesstype 

    syntax "{" lesstype:41 "with" lesstype:41 "<:" lesstype:41 "}": lesstype 
    syntax "{" lesstype:41 "}" : lesstype 

    syntax "forall" "[" lesstype "]" lesstype:41 "<:" lesstype:41 "have" lesstype:41 : lesstype 
    syntax "forall" "[" lesstype "]" lesstype:41 : lesstype 

    syntax "forall" lesstype:41 "<:" lesstype:41 "have" lesstype:41 : lesstype 
    syntax "forall" lesstype:41 : lesstype 

    syntax "induct" lesstype:40 : lesstype 

    syntax "(" lesstype ")" : lesstype

    syntax "⟨" term "⟩" : lesstype 

    syntax "[lesstype| " lesstype "]" : term

    macro_rules
    -- terminals
    | `([lesstype| $n:num ]) => `($n)
    | `([lesstype| $a:ident]) => `($(Lean.quote (toString a.getId)))
    -- Ty 
    | `([lesstype| β[$n] ]) => `(Ty.bvar [lesstype| $n ])
    | `([lesstype| α[$n:lesstype] ]) => `(Ty.fvar [lesstype| $n ])
    | `([lesstype| unit ]) => `(Ty.unit)
    | `([lesstype| ⊤ ]) => `(Ty.top)
    | `([lesstype| ⊥ ]) => `(Ty.bot)
    | `([lesstype| ? $a $b:lesstype ]) => `(Ty.tag [lesstype| $a ] [lesstype| $b ])
    | `([lesstype| $a : $b:lesstype ]) => `(Ty.field [lesstype| $a ] [lesstype| $b ])
    | `([lesstype| $a -> $b ]) => `(Ty.case [lesstype| $a ] [lesstype| $b ])
    | `([lesstype| $a | $b ]) => `(Ty.union [lesstype| $a ] [lesstype| $b ])
    | `([lesstype| $a & $b ]) => `(Ty.inter [lesstype| $a ] [lesstype| $b ])
    | `([lesstype| $a * $b ]) => `(Ty.inter (Ty.field "l" [lesstype| $a ]) (Ty.field "r" [lesstype| $b ]))

    | `([lesstype| { [$n] $d with $b <: $c }  ]) => `(Ty.exis [lesstype| $n ] [lesstype| $b ] [lesstype| $c ] [lesstype| $d ])
    | `([lesstype| { [$n] $b:lesstype } ]) => `(Ty.exis [lesstype| $n ] Ty.unit Ty.unit [lesstype| $b ] )

    | `([lesstype| { $d with $b <: $c }  ]) => 
      `(Ty.exis (Ty.infer_abstraction 0 [lesstype| $d ]) [lesstype| $b ] [lesstype| $c ] [lesstype| $d ])
    | `([lesstype| { $b:lesstype } ]) => 
      `(Ty.exis (Ty.infer_abstraction 0 [lesstype| $b ]) Ty.unit Ty.unit [lesstype| $b ] )

    | `([lesstype| forall $b <: $c have $d  ]) => 
      `(Ty.univ (Ty.infer_abstraction 0 [lesstype| $d ]) [lesstype| $b ] [lesstype| $c ] [lesstype| $d ])
    | `([lesstype| forall $b:lesstype  ]) => 
      `(Ty.univ (Ty.infer_abstraction 0 [lesstype| $b ]) Ty.unit Ty.unit [lesstype| $b ] )


    | `([lesstype| forall [$n] $b <: $c have $d  ]) => `(Ty.univ [lesstype| $n ] [lesstype| $b ] [lesstype| $c ] [lesstype| $d ])
    | `([lesstype| forall [$n] $b:lesstype  ]) => `(Ty.univ [lesstype| $n ] Ty.unit Ty.unit [lesstype| $b ] )


    | `([lesstype| induct $a ]) => `(Ty.recur [lesstype| $a ])

    | `([lesstype| ($a) ]) => `([lesstype| $a ])

    | `([lesstype| ⟨ $e ⟩ ]) => pure e


    partial def repr (ty : Ty) (n : Nat) : Format :=
    match ty with
    | .bvar id => 
      "β[" ++ Nat.repr id ++ "]"
    | .fvar id =>
      "α[" ++ Nat.repr id ++ "]"
    | .unit => "unit" 
    | .top => "⊤" 
    | .bot => "⊥" 
    | .tag l ty1 => 
      ("?" ++ l ++ " " ++ (repr ty1 n))
    | .field l ty1 => 
      Format.bracket "(" (l ++ " : " ++ (repr ty1 n)) ")"

    | .union ty1 ty2 =>
      let _ : ToFormat Ty := ⟨fun ty' => repr ty' n ⟩
      let tys := [ty1, ty2] 
      Format.bracket "("
        (Format.joinSep tys (" |" ++ Format.line))
      ")"
  
    | .inter (field "l" l) (field "r" r) =>
      Format.bracket "(" ((repr l n) ++ " * " ++ (repr r n)) ")"
    | .inter ty1 ty2 =>
      Format.bracket "(" ((repr ty1 n) ++ " & " ++ (repr ty2 n)) ")"
    | .case ty1 ty2 =>
      Format.bracket "(" ((repr ty1 n) ++ " ->" ++ Format.line ++ (repr ty2 n)) ")"
    | .exis n ty_c1 ty_c2 ty_pl =>
      if (ty_c1, ty_c2) == (.unit, .unit) then
        Format.bracket "{" (
          "[" ++ (Nat.repr n) ++ "] " ++
          repr ty_pl n
        ) "}"
      else
        Format.bracket "{" (
          "[" ++ (Nat.repr n) ++ "] " ++
          (repr ty_pl n) ++ " with " ++
          (repr ty_c1 n) ++ " <: " ++ (repr ty_c2 n)
        ) "}"
    | .univ n ty_c1 ty_c2 ty_pl =>
      if (ty_c1, ty_c2) == (.unit, .unit) then
        Format.bracket "(" ("forall [" ++ (Nat.repr n) ++ "] " ++ (repr ty_pl n)) ")"
      else
        Format.bracket "(" (
          "forall [" ++ (Nat.repr n) ++ "] " ++
          (repr ty_c1 n) ++ " <: " ++ (repr ty_c2 n) ++ " have " ++
          (repr ty_pl n)
        ) ")"
    | .recur ty1 =>
      Format.bracket "(" (
        "induct " ++ (repr ty1 n)
      ) ")"

    instance : Repr Ty where
      reprPrec := repr

    partial def subst (m : PHashMap Nat Ty) : Ty -> Ty
    | .bvar id => .bvar id 
    | .fvar id => (match m.find? id with
      | some ty => subst m ty 
      | none => .fvar id
    )
    | .unit => .unit
    | .top => .top
    | .bot => .bot
    | .tag l ty => .tag l (subst m ty) 
    | .field l ty => .field l (subst m ty)
    | .union ty1 ty2 => .union (subst m ty1) (subst m ty2)
    | .inter ty1 ty2 => .inter (subst m ty1) (subst m ty2)
    | .case ty1 ty2 => .case (subst m ty1) (subst m ty2)
    | .exis n ty_c1 ty_c2 ty => (.exis n
      (subst m ty_c1) (subst m ty_c2) 
      (subst m ty)
    )
    | .univ n ty_c1 ty_c2 ty => (.univ n
      (subst m ty_c1) (subst m ty_c2) 
      (subst m ty)
    )
    | .recur ty => .recur (subst m ty)

    -- assume assoc right
    def inter_contains : Ty -> Ty -> Bool 
    | ty1, inter ty21 ty22 => 
      inter_contains ty1 ty21 ||
      inter_contains ty1 ty22
    | ty1, ty2 => ty1 == ty2

    -- make assoc right
    def intersect : Ty -> Ty -> Ty
    | [lesstype| ⊤ ], ty2 => ty2 
    | bot, ty2 => bot 
    | inter ty11 ty12, ty2 => intersect ty11 (intersect ty12 ty2) 
    | ty1, [lesstype| ⊤ ] => ty1 
    | ty1, bot => bot 
    | ty1, ty2 => 
        if inter_contains ty1 ty2 then
          ty2
        else
          inter ty1 ty2


    -- assume assoc right
    def union_contains : Ty -> Ty -> Bool 
    | ty1, union ty21 ty22 => 
      union_contains ty1 ty21 ||
      union_contains ty1 ty22
    | ty1, ty2 => ty1 == ty2

    -- make assoc right
    def unionize : Ty -> Ty -> Ty
    | top, ty2 => top
    | bot, ty2 => ty2
    | union ty11 ty12, ty2 => unionize ty11 (unionize ty12 ty2) 
    | ty1, top => top 
    | ty1, bot => ty1
    | ty1, ty2 => 
        if union_contains ty1 ty2 then
          ty2
        else
          union ty1 ty2

    partial def simplify : Ty -> Ty
    | .bvar id => bvar id  
    | .fvar id => fvar id
    | .unit => .unit 
    | .top => .top
    | .bot => .bot 
    | .tag l ty => tag l (simplify ty) 
    | .field l ty => field l (simplify ty) 
    | .union ty1 ty2 => unionize (simplify ty1) (simplify ty2)
    | .inter ty1 ty2 => intersect (simplify ty1) (simplify ty2)
    | .case ty1 ty2 => case (simplify ty1) (simplify ty2)
    | .exis n cty1 cty2 ty => 
        exis n 
          (simplify cty1) (simplify cty2)
          (simplify ty)
    | .univ n cty1 cty2 ty => 
        univ n 
          (simplify cty1) (simplify cty2)
          (simplify ty)
    | .recur ty => recur (simplify ty)


    def reduce (env_ty : PHashMap Nat Ty) (ty : Ty) :=
      (simplify (subst (env_ty) ty))



    partial def free_vars: Ty -> PHashMap Nat Unit
    | .bvar id => {} 
    | .fvar id => PHashMap.from_list [(id, Unit.unit)] 
    | .unit => {} 
    | .top => {} 
    | .bot => {} 
    | .tag l ty => (free_vars ty) 
    | .field l ty => (free_vars ty)
    | .union ty1 ty2 => free_vars ty1 ; free_vars ty2
    | .inter ty1 ty2 => free_vars ty1 ; free_vars ty2
    | .case ty1 ty2 => free_vars ty1 ; free_vars ty2
    | .exis n ty_c1 ty_c2 ty =>
      -- (free_vars ty_c1);(free_vars ty_c2);(free_vars ty)
      (free_vars ty)
    | .univ n ty_c1 ty_c2 ty =>
      -- (free_vars ty_c1);(free_vars ty_c2);(free_vars ty)
      (free_vars ty)
    | .recur ty => (free_vars ty)

    partial def free_vars_env (env_ty : PHashMap Nat Ty) (ty : Ty) : PHashMap Nat Unit :=  
      free_vars (reduce env_ty ty)


    def signed_free_vars (posi : Bool) : Ty -> PHashMap Nat Unit
    | .bvar id => {} 
    | .fvar id => 
      if posi then
        let u : Unit := Unit.unit
        PHashMap.from_list [(id, u)] 
      else
        {}
    | .unit => {} 
    | .top => {} 
    | .bot => {} 
    | .tag l ty => (signed_free_vars posi ty) 
    | .field l ty => (signed_free_vars posi ty)
    | .union ty1 ty2 => signed_free_vars posi ty1 ; signed_free_vars posi ty2
    | .inter ty1 ty2 => signed_free_vars posi ty1 ; signed_free_vars posi ty2
    | .case ty1 ty2 => (signed_free_vars (!posi) ty1) ; signed_free_vars posi ty2
    | .exis n ty_c1 ty_c2 ty =>
      (signed_free_vars posi ty)
    | .univ n ty_c1 ty_c2 ty =>
      (signed_free_vars posi ty)
    | .recur ty => (signed_free_vars posi ty)


    def abstract (fids : List Nat) (start : Nat) : Ty -> Ty
    | .bvar id => .bvar id 
    | .fvar id => 
      match (fids.enumFrom start).find? (fun (_, fid) => fid == id) with
      | .some (bid, _) => .bvar bid
      | .none => .fvar id
    | .unit => .unit
    | .top => .top
    | .bot => .bot
    | .tag l ty => .tag l (abstract fids start ty) 
    | .field l ty => .field l (abstract fids start ty)
    | .union ty1 ty2 => .union (abstract fids start ty1) (abstract fids start ty2)
    | .inter ty1 ty2 => .inter (abstract fids start ty1) (abstract fids start ty2)
    | .case ty1 ty2 => .case (abstract fids start ty1) (abstract fids start ty2)
    | .exis n ty_c1 ty_c2 ty => 
      (.exis n
        (abstract fids (start + n) ty_c1) (abstract fids (start + n) ty_c2)
        (abstract fids (start + n) ty)
      )
    | .univ n ty_c1 ty_c2 ty => 
      (.univ n
        (abstract fids (start + n) ty_c1) (abstract fids (start + n) ty_c2)
        (abstract fids (start + n) ty)
      )
    | .recur ty => .recur (abstract fids (start + 1) ty)

    partial def reachable_constraints (env_ty : PHashMap Nat Ty) (ty : Ty) : List (Ty × Ty) :=
      let fvs := (free_vars ty).toList
      List.bind fvs (fun (key, _) =>
        match env_ty.find? (key) with
        | some ty' => (fvar key, ty') :: (reachable_constraints env_ty ty')
        | none => [] -- TODO: what if the key is inside a record?
      )

    def nested_pairs : (List Ty) -> Ty 
    | [] => .unit 
    | ty :: tys => [lesstype| ⟨ty⟩ * ⟨nested_pairs tys⟩ ]

    def generalize (boundary : Nat) (env_ty : PHashMap Nat Ty) (ty : Ty) : Ty := 
      -- avoids substitution, as type variable determines type adjustment
      -- boundary prevents overgeneralizing
      let constraints := reachable_constraints env_ty ty
      let (lhs, rhs) := List.unzip constraints
      let ty_lhs := nested_pairs lhs
      let ty_rhs := nested_pairs rhs

      let fids := List.filter (fun id => id >= boundary) (
          (free_vars ty; free_vars ty_lhs ; free_vars ty_rhs).toList.bind (fun (k , _) => [k])
      )

      if fids.isEmpty then
        ty
      else
        [lesstype|
          forall [⟨fids.length⟩] ⟨abstract fids 0 ty_lhs⟩ <: ⟨abstract fids 0 ty_rhs⟩ have 
          ⟨abstract fids 0 ty⟩
        ]


    def instantiate (start : Nat) (args : List Ty) : Ty -> Ty
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
    | .top => .top
    | .bot => .bot
    | .tag l ty => .tag l (instantiate start args ty) 
    | .field l ty => .field l (instantiate start args ty)
    | .union ty1 ty2 => .union (instantiate start args ty1) (instantiate start args ty2)
    | .inter ty1 ty2 => .inter (instantiate start args ty1) (instantiate start args ty2)
    | .case ty1 ty2 => .case (instantiate start args ty1) (instantiate start args ty2)
    | .exis n ty_c1 ty_c2 ty => 
      (.exis n
        (instantiate (start + n) args ty_c1) (instantiate (start + n) args ty_c2)
        (instantiate (start + n) args ty)
      )
    | .univ n ty_c1 ty_c2 ty => 
      (.univ n
        (instantiate (start + n) args ty_c1) (instantiate (start + n) args ty_c2)
        (instantiate (start + n) args ty)
      )
    | .recur ty => .recur (instantiate (start + 1) args ty)


    partial def roll_recur (key : Nat) (m : PHashMap Nat Ty) (ty : Ty) : Ty :=
      if (free_vars_env m ty).contains key then
        subst (PHashMap.from_list [(key, [lesstype| β[0] ])]) [lesstype| (induct ⟨ty⟩) ] 
      else
        ty 

    partial def occurs_not (key : Nat) (m : PHashMap Nat Ty) (ty : Ty) : Ty :=
      if (free_vars_env m ty).contains key then
        bot
      else
        ty


    partial def subst_default (sign : Bool) : Ty -> Ty
    | .bvar id => bvar id  
    | .fvar id => if sign then bot else [lesstype| ⊤ ] 
    | .unit => .unit 
    | .top => .top
    | .bot => .bot 
    | .tag l ty => tag l (subst_default sign ty) 
    | .field l ty => field l (subst_default sign ty) 
    | .union ty1 ty2 =>
      union (subst_default sign ty1) (subst_default sign ty2)
    | .inter ty1 ty2 =>
      inter (subst_default sign ty1) (subst_default sign ty2)
    | .case ty1 ty2 => case (subst_default (!sign) ty1) (subst_default sign ty2)
    | .exis n cty1 cty2 ty => 
        -- can't sub away if constrained
        exis n cty1 cty2 ty
    | .univ n cty1 cty2 ty => 
        -- can't sub away if constrained
        univ n cty1 cty2 ty
    | .recur ty => recur (subst_default sign ty)


    partial def equal (env_ty : PHashMap Nat Ty) (ty1 : Ty) (ty2 : Ty) : Bool :=
      let ty1 := simplify (Ty.subst env_ty ty1)
      let ty2 := simplify (Ty.subst env_ty ty2)
      ty1 == ty2

    def split_intersectionss : Ty -> List Ty 
    | Ty.inter ty1 ty2 =>
      (split_intersectionss ty1) ++ (split_intersectionss ty2)
    | ty => [ty]

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
    | .fvar _ => some [] 
    | _ => none

    def extract_nested_fields : Ty -> (List Ty)
    | .field l ty => [ty]
    | .inter (.field l ty1) ty2 => 
      match extract_nested_fields ty1 with
      | [] => ty1 :: (extract_nested_fields ty2)
      | nested_fields =>
        nested_fields ++ (extract_nested_fields ty2)
    | .inter ty1 (.field l ty2) => 
      match extract_nested_fields ty2 with
      | [] => ty2 :: (extract_nested_fields ty1)
      | nested_fields => nested_fields ++ (extract_nested_fields ty1)
    | _ => [] 

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

    partial def extract_label_list (ty : Ty) : List String :=
      (extract_record_labels ty).toList.map fun (l, _) => l

    partial def wellfounded (n : Nat) : Ty -> Bool
    | .bvar id => (List.range n).all (fun tar => id != tar)
    | .fvar _ => true 
    | .unit => true 
    | .top => true 
    | .bot => true 
    | .tag _ _ => true 
    | .field _ ty => Ty.wellfounded n ty
    | .union ty1 ty2 =>
      Ty.wellfounded n ty1 && Ty.wellfounded n ty2
    | .inter ty1 ty2 =>
      match (extract_nested_fields (inter ty1 ty2)) with
      | [] => false
      | fields => fields.any (fun ty' => Ty.wellfounded n ty')
    | .case _ _ => false
    | .exis n' ty_c1 ty_c2 ty' => 
      Ty.wellfounded (n + n') ty'
    | .univ _ _ _ _ => false 
    | .recur _ => false 

    def matchable (fields : List Ty) : Bool := 
      List.any fields (fun ty_fd =>
        match ty_fd with
        | Ty.tag _ _ => true 
        | _ => false
      )  

    def split_unions : Ty -> List Ty 
    | Ty.union ty1 ty2 =>
      (split_unions ty1) ++ (split_unions ty2)
    | ty => [ty]

    def extract_field (label : String) (ty : Ty) : Option Ty := do
      let fields <- (linearize_fields ty)
      let fields_filt := fields.filter (fun (l, _) => l == label)
      if h : fields_filt.length > 0 then
        let (_, ty_fd) := (fields_filt.get ⟨0, h⟩)
        some ty_fd
      else
        none

    def extract_field_induct (label : String): Ty -> Option Ty 
    | .exis n ty (.bvar id) ty_pl => 
      -- assume β[n] is the inductive fixed point 
      if id == n then
        Option.bind (extract_field label ty) (fun ty => 
        Option.bind (extract_field label ty_pl) (fun ty_pl =>
          (Ty.exis n  ty (.bvar id) ty_pl)
        ))
      else 
        none
    | ty => extract_field label ty 

    -- from induction over union of intersections to intersection of induction over union
    partial def transpose_relation (labels : List String) : Ty -> Ty
    | Ty.recur ty =>
      let unions := split_unions ty
      labels.foldr (fun label ty_acc =>
        let ty_col := unions.foldr (fun ty_row ty_col =>
          match extract_field_induct label ty_row with
          | some ty_field => Ty.union ty_field ty_col 
          | none => Ty.top
        ) Ty.bot 
        Ty.inter (Ty.field label (Ty.recur ty_col)) ty_acc 
      ) Ty.top
    | ty => 
      Ty.top
      -- let unions := split_unions ty
      -- labels.foldr (fun label ty_acc =>
      --   let ty_col := unions.foldr (fun ty_row ty_col =>
      --     match extract_field label ty_row with
      --     | some ty_field => Ty.union ty_field ty_col 
      --     | none => Ty.top
      --   ) Ty.bot 
      --   Ty.inter (Ty.field label ty_col) ty_acc 
      -- ) Ty.top




    -- def extract_field (start : Nat) (label : String): Ty -> Option Ty 
    -- | .univ n [lesstype| unit ] [lesstype| unit ] ty3 => 
    --   Option.bind (extract_field (start + n) ty3) (fun ty3_prem =>
    --     (Ty.exis n [lesstype| unit ] [lesstype| unit ] ty3_prem)
    --   )
    -- | .univ n (.bvar id) ty0  ty3 => 
    --   if id == start + n then
    --     Option.bind (extract_field (start + n) ty0) (fun ty0_prem => 
    --     Option.bind (extract_field (start + n) ty3) (fun ty3_prem =>
    --       (Ty.exis n ty0_prem (.bvar (start + n)) ty3_prem)
    --     ))
    --   else 
    --     none
    -- | Ty.inter ty1 Ty.top => 
    --   (extract_field start ty1)
    -- | Ty.inter ty1 (Ty.fvar _) => 
    --   (extract_field start ty1)
    -- | Ty.inter Ty.top ty2 => 
    --   (extract_field start ty2)
    -- | Ty.inter (Ty.fvar _) ty2 => 
    --   (extract_field start ty2)
    -- | Ty.inter ty1 ty2 => 
    --   Option.bind (extract_field start ty1) (fun ty1_prem =>
    --   Option.bind (extract_field start ty2) (fun ty2_prem =>
    --     Ty.union ty1_prem ty2_prem
    --   ))
    -- | Ty.case ty1 _ => some ty1 
    -- | _ => none

    partial def unify (i : Nat) (env_ty : PHashMap Nat Ty) (env_complex : PHashMap (Dir × Ty) Ty)
    (frozen : PHashMap Nat Unit):
    Ty -> Ty -> (Nat × List (PHashMap Nat Ty))

    -- liberally quantified 
    | ty', .exis n ty_c1 ty_c2 ty =>
      let (i, args, frozen) := (
        i + n, 
        (List.range n).map (fun j => .fvar (i + j)),
        PHashMap.insert_all frozen (PHashMap.from_list ((List.range n).map (fun j => (i + j, .unit))))
      )

      let ty_c1 := Ty.instantiate 0 args ty_c1
      let ty_c2 := Ty.instantiate 0 args ty_c2
      let ty := Ty.instantiate 0 args ty
      assume_env (unify i env_ty env_complex frozen ty' ty) (fun i env_ty => 
        unify i env_ty env_complex frozen ty_c1 ty_c2
      )

    -- opaquely quantified 
    | .exis n ty_c1 ty_c2 ty1, ty2 =>
      let bound_start := i
      let (i, ids) := (i + n, (List.range n).map (fun j => i + j))
      let bound_end := i
      let is_bound_var := (fun i' => bound_start <= i' && i' < bound_end)

      let args := ids.map (fun id => Ty.fvar id)
      let ty_c1 := Ty.instantiate 0 args ty_c1
      let ty_c2 := Ty.instantiate 0 args ty_c2
      let ty1 := Ty.instantiate 0 args ty1

      let op_fields := linearize_fields ty_c1

      let ((i, contexts), env_complex) := ( 
        match op_fields with 
        | .none => (unify i (env_ty) env_complex frozen ty_c1 ty_c2, env_complex)
        | .some fields =>
          let is_recur_type := match ty_c2 with 
          | Ty.recur _ => true
          | _ => false
          let is_consistent_variable_record := List.all fields (fun (l, _) =>
            let rlabels := extract_record_labels (ty_c2) 
            rlabels.contains l 
          )
          let unmatchable := !(matchable (extract_nested_fields (Ty.simplify (Ty.subst env_ty ty_c1))))
          if is_recur_type && unmatchable  then 
            if is_consistent_variable_record then
              let labels := extract_label_list ty_c1
              let ty_c2 := (transpose_relation labels ty_c2)

              let ty_norm := ty_c1 
              (unify i env_ty env_complex frozen ty_c1 ty_c2, env_complex.insert (.dn, ty_norm) ty_c2)
            else 
              ((i, []), env_complex) 
          else
            (unify i (env_ty) env_complex frozen ty_c1 ty_c2, env_complex)
      )

      -- vacuous truth unsafe: given P |- Q, if P is incorreclty false, then P |- Q is incorrecly true (which is unsound)
      -- Option.bind op_context (fun (i, env_ty1) =>
      assume_env (i, contexts) (fun i env_ty => 
      let locally_constrained := (fun key => env_ty.contains key)
      assume_env (unify i env_ty env_complex frozen ty1 ty2) (fun i env_ty =>
        let is_result_safe := List.all env_ty.toList (fun (key, ty_value) =>
          not (is_bound_var key) || (locally_constrained key)
        )
        if is_result_safe then
          (i, [env_ty])
        else
          (i, [])
      ))

    -- liberally quantified universal 
    | .univ n ty_c1 ty_c2 ty1, ty2 =>
      let (i, args) := (
        i + n, 
        (List.range n).map (fun j => .fvar (i + j))
      )

      let ty_c1 := Ty.instantiate 0 args ty_c1
      let ty_c2 := Ty.instantiate 0 args ty_c2
      let ty1 := Ty.instantiate 0 args ty1
      -- assume_env (unify i env_ty env_complex frozen ty1 ty2) (fun i env_ty => 
      --   unify i env_ty env_complex frozen ty_c1 ty_c2
      -- )
      assume_env (unify i env_ty env_complex frozen ty_c1 ty_c2) (fun i env_ty => 
        (unify i env_ty env_complex frozen ty1 ty2)
      )

    -- opaquely quantified universal 
    | ty1, .univ n ty_c1 ty_c2 ty2  =>
      let bound_start := i
      let (i, ids) := (i + n, (List.range n).map (fun j => i + j))
      let bound_end := i
      let is_bound_var := (fun i' => bound_start <= i' && i' < bound_end)

      let args := ids.map (fun id => Ty.fvar id)
      let ty_c1 := Ty.instantiate 0 args ty_c1
      let ty_c2 := Ty.instantiate 0 args ty_c2
      let ty2 := Ty.instantiate 0 args ty2

      let ((i, contexts), env_complex) := ( 
          (unify i (env_ty) env_complex frozen ty_c1 ty_c2, env_complex)
      )

      -- vacuous truth unsafe: given P |- Q, if P is incorreclty false, then P |- Q is incorrecly true (which is unsound)
      -- Option.bind op_context (fun (i, env_ty1) =>
      assume_env (i, contexts) (fun i env_ty => 
      let locally_constrained := (fun key => env_ty.contains key)
      assume_env (unify i env_ty env_complex frozen ty1 ty2) (fun i env_ty =>
        let is_result_safe := List.all env_ty.toList (fun (key, ty_value) =>
          not (is_bound_var key) || (locally_constrained key)
        )
        if is_result_safe then
          (i, [env_ty])
        else
          (i, [])
      ))

    -- free variables
    ---------------------------------------------------------------
    | (.fvar id1), (.fvar id2) => 
      match (env_ty.find? id1, env_ty.find? id2) with 
      | (.none, .none) => 
        -- ensure older unassigned free variables appear in simplified form
        if id1 < id2 then
          (i, [env_ty.insert id2 (Ty.fvar id1)])
        else if id1 > id2 then
          (i, [env_ty.insert id1 (Ty.fvar id2)])
        else
          (i, [env_ty])
      | (_, .some ty) => unify i env_ty env_complex frozen (.fvar id1) ty 
      | (.some ty', _) => unify i env_ty env_complex frozen ty' (.fvar id2) 

    | .fvar id, ty  => 
      match env_ty.find? id with 
      | none => 
        (i, [env_ty.insert id (occurs_not id env_ty ty)])
      | some ty' => 
        let adjustable := frozen.find? id == .none
        let (i, u_env_ty) := (unify i env_ty env_complex frozen ty' ty)
        if adjustable && u_env_ty.isEmpty then
          (i, [env_ty.insert id (occurs_not id env_ty (Ty.inter ty ty'))])
        else
          (i, u_env_ty)

    | ty', .fvar id => 
      match env_ty.find? id with 
      | none => 
        (i, [env_ty.insert id (roll_recur id env_ty ty')])
      | some ty => 
        let adjustable := frozen.find? id == .none
        let (i, u_env_ty) := (unify i env_ty env_complex frozen ty' ty) 
        if adjustable && u_env_ty.isEmpty then
          (i, [env_ty.insert id (roll_recur id env_ty (Ty.union ty' ty))])
        else
          (i, u_env_ty)


    | .case ty1 ty2, .case ty3 ty4 =>

      assume_env (unify i env_ty env_complex frozen ty3 ty1) (fun i env_ty =>
        (unify i env_ty env_complex frozen ty2 ty4)
      ) 

    | .bvar id1, .bvar id2  =>
      if id1 = id2 then 
        (i, [env_ty])
      else
        (i, [])

    | .bot, _ => (i, [env_ty])
    | _, .top => (i, [env_ty])
    | .unit, .unit => (i, [env_ty])

    | .tag l' ty', .tag l ty =>
      if l' = l then
        unify i env_ty env_complex frozen ty' ty
      else
        (i, [])

    | .field l' ty', .field l ty =>
      if l' == l then
        unify i env_ty env_complex frozen ty' ty
      else
        (i, [])


    | .recur ty1, .recur ty2 =>
      if Ty.equal env_ty ty1 ty2 then
        (i, [env_ty])
      else
        -- unroll using rhs ty
        -- by induction hypothesis, ty1 ≤ ty2
        let ty1' := Ty.instantiate 0 [Ty.recur ty2] ty1
        let ty2' := Ty.instantiate 0 [Ty.recur ty2] ty2
        unify i env_ty env_complex frozen ty1' ty2'

    | ty', .recur ty =>
      let ty' := (Ty.simplify (Ty.subst env_ty ty'))
      match (extract_nested_fields ty') with
      | [] => 
        if Ty.wellfounded 1 ty then
          unify i env_ty env_complex frozen ty' (Ty.instantiate 0 [Ty.recur ty] ty) 

        else
          (i, []) 
      | fields =>
        if matchable fields then 
          if Ty.wellfounded 1 ty then
            unify i env_ty env_complex frozen ty' (Ty.instantiate 0 [Ty.recur ty] ty)
          else
            (i, []) 
        else
          let ty_norm := ty'
          match env_complex.find? (.dn, ty_norm) with
          | .some ty_cache => 
            unify i env_ty env_complex frozen ty_cache (Ty.recur ty)
          | .none =>  
            (i, []) 

    | Ty.union ty1 ty2, ty => 
      assume_env (unify i env_ty env_complex frozen ty1 ty) (fun i env_ty =>
        (unify i env_ty env_complex frozen ty2 ty)
      )

    | ty, .union ty1 ty2 => 
      let (i, u_env_ty1) := (unify i env_ty env_complex frozen ty ty1)
      let (i, u_env_ty2) := (unify i env_ty env_complex frozen ty ty2)
      (i, u_env_ty1 ++ u_env_ty2)


    | ty, .inter ty1 ty2 => 
      assume_env (unify i env_ty env_complex frozen ty ty1) (fun i env_ty =>
        (unify i env_ty env_complex frozen ty ty2)
      )

    | .inter ty1 ty2, ty => 
      let (i, u_env_ty1) := (unify i env_ty env_complex frozen ty1 ty)
      let (i, u_env_ty2) := (unify i env_ty env_complex frozen ty2 ty)
      (i, u_env_ty1 ++ u_env_ty2)

    | _, _ => (i, []) 

    partial def union_all : (List Ty) -> Option Ty
      | [] => none
      | t::ts =>
        let ts := List.filter
          (fun t' => not (t == t'))
          ts
        match union_all ts with
          | .none => .some t
          | .some t' => union t t'


    partial def unify_reduce_env (i : Nat) (env_ty : PHashMap Nat Ty) (ty1) (ty2) (ty_result) :=
      let (_, u_env_ty) := (unify i env_ty {} {} ty1 ty2)
      List.foldr (fun env_ty ty_acc => 
        simplify (subst env_ty (union ty_result ty_acc))
      ) bot u_env_ty

    partial def unify_reduce (i : Nat) (ty1) (ty2) (ty_result) :=
      let (_, u_env_ty) := (unify i {} {} {} ty1 ty2)
      List.foldr (fun env_ty ty_acc => 
        simplify (subst env_ty (union ty_result ty_acc))
      ) bot u_env_ty


    partial def unify_simple (i : Nat) (ty1) (ty2) :=
      (unify i {} {} {} ty1 ty2)

    partial def unify_decide (i : Nat) (ty1) (ty2) :=
      let (_, result) := (unify i {} {} {} ty1 ty2)
      !result.isEmpty

    def combine (i_u_env_ty : (Nat × List (PHashMap Nat Ty))) (ty : Ty) :=
      let (i, u_env_ty) := i_u_env_ty
      (i, u_env_ty.map fun env_ty => (env_ty, ty))

    def to_pair_type : Ty -> Ty 
    | case ty1 ty2 => 
      [lesstype| ⟨ty1⟩ * ⟨ty2⟩ ] 
    | [lesstype| ⊤ ] =>  [lesstype| ⊥ ]
    | _ =>  [lesstype| ⊤ ]


  end Ty

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
  | letb : Option Ty -> Tm -> Tm -> Tm
  | fix : Tm -> Tm
  deriving Repr, Inhabited, BEq


  namespace Tm

    declare_syntax_cat lessterm 
    syntax:100 num : lessterm 
    syntax:100 ident : lessterm 
    syntax:30 "_" : lessterm
    syntax:30 "()" : lessterm
    syntax:30 "y[" lessterm:90 "]": lessterm
    syntax:30 "x[" lessterm:90 "]" : lessterm
    syntax:30 "#" lessterm:100 lessterm:30 : lessterm

    syntax:30 "@" lessterm:100 "=" lessterm:30 : lessterm
    syntax:30 "@" lessterm:100 "=" lessterm:30 lessterm: lessterm

    syntax "{" lessterm,+ "}" : lessterm 
    syntax:30 "(" lessterm "," lessterm ")" : lessterm

    syntax:20 "\\" lessterm:30 "=>" lessterm:20 : lessterm
    syntax:20 "\\" lessterm:30 "=>" lessterm:20 lessterm: lessterm

    syntax:30 lessterm:30 "." lessterm:100 : lessterm 
    syntax:30 "(" lessterm:30 lessterm:30 ")" : lessterm 
    syntax:30 "let y[0]" ":" lesstype:30 "=" lessterm:30 "in" lessterm:30 : lessterm 
    syntax:30 "let y[0]" "=" lessterm:30 "in" lessterm:30 : lessterm 
    syntax:30 "fix " lessterm:30 : lessterm 

    syntax "(" lessterm ")" : lessterm

    syntax "⟨" term "⟩" : lessterm 

    syntax "[lessterm| " lessterm "]" : term

    def record_fields : Tm -> List (String × Tm)
    | record fields => fields
    | _ =>  []

    def function_cases : Tm -> List (Tm × Tm)
    | func cases => cases 
    | _ =>  []

    macro_rules
    | `([lessterm| $n:num ]) => `($n)
    | `([lessterm| $a:ident]) => `($(Lean.quote (toString a.getId)))
    | `([lessterm| _ ]) => `(Tm.hole)
    | `([lessterm| () ]) => `(Tm.unit)
    | `([lessterm| y[$n] ]) => `(Tm.bvar [lessterm| $n ])
    | `([lessterm| x[$n] ]) => `(Tm.fvar [lessterm| $n ])
    | `([lessterm| # $a $b ]) => `(Tm.tag [lessterm| $a ] [lessterm| $b ])

    | `([lessterm| @ $a = $b ]) => `( Tm.record [ ([lessterm| $a ], [lessterm| $b ]) ]  )
    | `([lessterm| @ $a = $b $xs ]) => `( Tm.record (([lessterm| $a ], [lessterm| $b ]) :: (Tm.record_fields [lessterm| $xs ])))

    | `([lessterm| ( $a , $b ) ]) => `(Tm.record [("l", [lessterm| $a ]), ("r", [lessterm|$b ])])

    | `([lessterm| \ $b => $d ]) => `(Tm.func [([lessterm| $b ], [lessterm| $d ])])
    | `([lessterm| \ $b => $d $xs ]) => `( Tm.func (([lessterm| $b ], [lessterm| $d ]) :: (Tm.function_cases [lessterm| $xs ])))


    | `([lessterm| $a . $b ]) => `(Tm.proj [lessterm| $a ] [lessterm| $b ])
    | `([lessterm| ($a $b) ]) => `(Tm.app [lessterm| $a ] [lessterm| $b ])
    | `([lessterm| let y[0] : $a = $b in $c ]) => `(Tm.letb (Option.some [lesstype| $a ]) [lessterm| $b ] [lessterm| $c ])
    | `([lessterm| let y[0] = $b in $c ]) => `(Tm.letb Option.none [lessterm| $b ] [lessterm| $c ])
    | `([lessterm| fix $a ]) => `(Tm.fix [lessterm| $a ])

    -- generic
    | `([lessterm| ($a) ]) => `([lessterm| $a ])

    --escape 
    | `([lessterm| ⟨ $e ⟩ ]) => pure e


    #eval [lesstype| forall β[0] -> {β[0] with β[0] <: β[1] * β[2] }  ]

    #eval [lesstype| forall β[0] -> {β[0] | unit with β[1] <: β[0] } ]


    partial def repr (t : Tm) (n : Nat) : Format :=
    match t with
    | .hole => 
      "_"
    | .unit =>
      "()"
    | .bvar id =>
      "y[" ++ (Nat.repr id) ++ "]"
    | .fvar id => 
      "x[" ++ (Nat.repr id) ++ "]"
    | .tag l t1 =>
      "#" ++ l ++ " " ++ (repr t1 n)
    | record [("l", l), ("r", r)] =>
      let _ : ToFormat Tm := ⟨fun t1 => repr t1 n ⟩
      Format.bracket "(" (Format.joinSep [l, r] ("," ++ Format.line)) ")"
    | record fds =>
      let _ : ToFormat (String × Tm) := ⟨fun (l, t1) => "@" ++ l ++ " = " ++ repr t1 n⟩
      Format.bracket "(" (Format.joinSep fds (" " ++ Format.line)) ")"
    | func fs =>
      let _ : ToFormat (Tm × Tm) := ⟨fun (pat, tb) =>
        "| " ++ (repr pat n) ++ " => " ++ (repr tb (n))
      ⟩
      Format.bracket "(" (Format.joinSep fs (" " ++ Format.line)) ")"
    | .proj t1 l =>
      repr t1 n ++ "/" ++ l
    | .app t1 t2 =>
      Format.bracket "(" (repr t1 n) ") " ++ "(" ++ repr t2 n ++ ")"
    | .letb op_ty1 t1 t2 =>
      match op_ty1 with
      | some ty1 =>
        "let y[0] : " ++ (Ty.repr ty1 n) ++ " = " ++  (repr t1 n) ++ " in" ++
        Format.line  ++ (repr t2 n) 
      | none =>
        "let y[0] = " ++  (repr t1 n) ++ " in" ++
        Format.line  ++ (repr t2 n) 
    | .fix t1 =>
      Format.bracket "(" ("fix " ++ (repr t1 n)) ")"

    instance : Repr Tm where
      reprPrec := repr

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

    partial def abstract (fids : List Nat) (start : Nat) : Tm -> Tm
    | .hole => hole 
    | .unit => .unit 
    | .bvar id => bvar id 
    | .fvar id => 
      match (fids.enumFrom start).find? (fun (_, fid) => fid == id) with
      | .some (bid, _) => .bvar bid
      | .none => .fvar id 
    | .tag l t => .tag l (abstract fids start t) 
    | .record fds =>
      record (List.map (fun (l, t) =>
        (l, abstract fids start t)
      ) fds)
    | .func fs =>
      func (List.map (fun (tp, tb) =>
        let n := match pattern_wellformed 0 tp with
        | .some n => n 
        | .none => 0 
        let tp := abstract fids (start + n) tp 
        let tb := abstract fids (start + n) tb
        (tp, tb)
      ) fs)
    | .proj t l => 
      proj (abstract fids start t) l
    | .app t1 t2 =>
      app 
        (abstract fids start t1) 
        (abstract fids start t2)
    | .letb ty1 t1 t2 =>
      letb ty1 
        (abstract fids start t1)
        (abstract fids (start + 1) t2)
    | .fix t =>
      .fix (abstract fids start t)


    partial def instantiate (start : Nat) (args : List Tm) : Tm -> Tm
    | .hole => hole 
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
    | .tag l t => tag l (instantiate start args t)
    | .record fds =>
      record (List.map (fun (l, t) =>
        (l, instantiate start args t)
      ) fds)
    | .func fs =>
      func (List.map (fun (tp, tb) =>
        let n := match pattern_wellformed 0 tp with
        | .some n => n 
        | .none => 0 
        let tp := instantiate (start + n) args tp 
        let tb := instantiate (start + n) args tb
        (tp, tb)
      ) fs)
    | .proj t l => 
      proj (instantiate start args t) l
    | .app t1 t2 =>
      app 
        (instantiate start args t1) 
        (instantiate start args t2)
    | .letb ty1 t1 t2 =>
      letb ty1 
        (instantiate start args t1)
        (instantiate (start + 1) args t2)
    | .fix t =>
      .fix (instantiate start args t)



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


    partial def infer (i : Nat) (env_ty : PHashMap Nat Ty) (env_tm : PHashMap Nat Ty) (t : Tm) (ty : Ty) : 
    (Nat × List (PHashMap Nat Ty × Ty)) :=
    match t with
    | hole => 
      let (i, ty') := (i + 1, Ty.fvar i)
      let (i, u_env_ty) := (Ty.unify i env_ty {} {} ty' ty) 
      (i, u_env_ty.map fun env_ty => (env_ty, ty'))
    | .unit => 
      let (i, u_env_ty) := (Ty.unify i env_ty {} {} Ty.unit ty) 
      (i, u_env_ty.map fun env_ty => (env_ty, Ty.unit))
    | bvar _ => (i, []) 
    | fvar id =>
      match (env_tm.find? id) with
      | some ty' => 
        Ty.combine (Ty.unify i env_ty {} {} ty' ty) ty'
      | none => (i, [])

    | .tag l t1 =>   
      let (i, ty1) := (i + 1, Ty.fvar i)
      assume_env (Ty.unify i env_ty {} {} (Ty.tag l ty1) ty) (fun i env_ty =>
      assume_env (infer i env_ty env_tm t1 ty1) (fun i (env_ty, ty1') =>
        (i, [(env_ty, Ty.tag l ty1')])
      ))

    | .record fds =>
      let (i, trips) := List.foldr (fun (l, t1) (i, ty_acc) =>
        (i + 1, (l, t1, (Ty.fvar i)) :: ty_acc)
      ) (i, []) fds

      let ty_init := [lesstype| ⊤ ] 

      let ty' := List.foldr (fun (l, _, ty1) ty_acc => 
        Ty.inter (Ty.field l ty1) ty_acc 
      ) ty_init trips 

      let f_step := (fun (l, t1, ty1) acc =>
        assume_env acc (fun i (env_ty, ty_acc) =>
        assume_env (infer i env_ty env_tm t1 ty1) (fun i (env_ty, ty1') =>
          (i, [(env_ty, Ty.inter (Ty.field l ty1') ty_acc)])
        ))
      )

      let init := Ty.combine (Ty.unify i env_ty {} {} ty' ty) [lesstype| ⊤ ]
      List.foldr f_step init trips

    | .func fs =>
      let (i, fs_typed) := List.foldr (fun (p, b) (i, ty_acc) =>
        (i + 2, (p, Ty.fvar i, b, Ty.fvar (i + 1)) :: ty_acc)
      ) (i, []) fs

      let case_init := [lesstype| ⊤ ]

      let (i, ty') := List.foldr (fun (p, ty_p, b, ty_b) (i, ty_acc) => 
        (i, Ty.inter (Ty.case ty_p ty_b) ty_acc) 
      ) (i, case_init) fs_typed 

      let f_step := (fun (p, ty_p, b, ty_b) acc =>
        assume_env acc (fun i (env_ty, ty_acc) =>
        match pattern_wellformed 0 p with
        | none => (i, [])
        | some n =>
          let env_pat : PHashMap Nat Ty := (List.range n).foldl (init := {}) (fun env_pat j => 
            let tm_key := (i + (2 * j))
            let ty_x := Ty.fvar (i + (2 * j) + 1) 
            (env_pat.insert tm_key ty_x)
          )
          let i := i + (2 * n)

          let list_tm_x := env_pat.toList.map (fun (k, _) => (fvar k))

          let p := instantiate 0 list_tm_x p 
          let b := instantiate 0 list_tm_x b  
          assume_env (infer i env_ty (env_tm ; env_pat) p ty_p) (fun i (env_ty, ty_p') =>
          assume_env (infer i env_ty (env_tm ; env_pat) b ty_b) (fun i (env_ty, ty_b') =>
              (i, [(env_ty, Ty.simplify (Ty.inter (Ty.case ty_p' ty_b') ty_acc))])
          )))
        )

      let init := Ty.combine (Ty.unify i env_ty {} {} ty' ty) [lesstype| ⊤ ]
      List.foldr f_step init fs_typed

    | .proj t1 l =>
      assume_env (infer i env_ty env_tm t1 (Ty.field l ty)) (fun i (env_ty, ty1') =>
      let (i, ty') := (i + 1, Ty.fvar i)
      assume_env (Ty.unify i env_ty {} {} ty1' (Ty.field l ty')) (fun i env_ty =>
        (i, [(env_ty, ty')])
      ))

    | .app t1 t2 =>
      assume_env (infer i env_ty env_tm t2 [lesstype| ⊤ ]) (fun i (env_ty, ty2') =>
      assume_env (infer i env_ty env_tm t1 (Ty.case ty2' ty)) (fun i (env_ty, ty1) =>
      let (i, ty') := (i + 1, Ty.fvar i)
      assume_env (Ty.unify i env_ty {} {} ty1 (Ty.case ty2' ty')) (fun i env_ty =>
        (i, [(env_ty, ty')])
      )))

    | .letb op_ty1 t1 t => 

      let (i, ty1) := match op_ty1 with
      | some ty1 => (i, ty1)
      | none => (i + 1, Ty.fvar i)

      let free_var_boundary := i
      assume_env (infer i env_ty env_tm t1 ty1) (fun i (env_ty, ty1') =>
        let ty1_schema := Ty.generalize free_var_boundary env_ty ty1'

        let (i, x, env_tmx) := (i + 1, fvar i, PHashMap.from_list [(i, ty1_schema)]) 
        let t := instantiate 0 [x] t 

        (infer i env_ty (env_tm ; env_tmx) t ty) 
      )

    | .fix t1 =>
      let (i, ty_prem) := (i + 1, Ty.fvar i) 
      let (i, ty_conc) := (i + 1, Ty.fvar i) 
      assume_env (infer i env_ty env_tm t1 (Ty.case ty_prem ty_conc)) (fun i (env_ty, _) =>
      -- assume_env (Ty.unify i env_ty {} ty1' (.case ty_prem ty)) (fun i env_ty =>
        let ty_prem := Ty.reduce env_ty ty_prem 
        let ty_conc := Ty.reduce env_ty ty_conc

        let ty_content := List.foldr (fun ty_case ty_acc =>
          let fvs := (Ty.free_vars ty_case).toList.bind (fun (k , _) => [k])
          let fvs_prem :=  (Ty.free_vars ty_prem)
          let ty_choice := (
            if List.any fvs (fun id => fvs_prem.find? id != none) then
              let fixed_point := fvs.length
              [lesstype|
                {[⟨fvs.length⟩] ⟨Ty.abstract fvs 0 (Ty.to_pair_type ty_case)⟩ with 
                  ⟨Ty.abstract fvs 0 (Ty.to_pair_type ty_prem)⟩ <: β[⟨fixed_point⟩] 
                } 
              ]
            else if fvs.length > 0 then
              [lesstype| {[⟨fvs.length⟩] ⟨Ty.abstract fvs 0 (Ty.to_pair_type ty_case)⟩} ]
            else
              (Ty.to_pair_type ty_case)
          )

          (Ty.union ty_choice ty_acc) 
        ) [lesstype| ⊥ ] (Ty.split_intersectionss ty_conc)

        -- constraint that ty' <= ty_prem is built into inductive type
        let relational_type := [lesstype| induct ⟨ty_content⟩ ]
        -- TODO: need to add constraint to premise to avoid being too strong: 
          -- i.e. premise accepts anything and conclusion becomes false.
          -- Actually, lack of annotation means weakest precondition
        let ty' := [lesstype| forall [1] β[0] -> {[1] β[0] with β[1] * β[0] <: ⟨relational_type⟩} ] 
        assume_env (Ty.unify i env_ty {} {} ty' ty) (fun i env_ty =>
          (i, [(env_ty, ty')])
        )
        -- (i, [(env_ty, ty')])
      )
      -- )


    partial def infer_simple i (t : Tm) :=
      (infer (i + 1) {} {} t (Ty.fvar i))

    partial def infer_reduce_wt (i : Nat) (t : Tm) (ty : Ty): Ty :=
      let boundary := i
      let (_, u_env) := (infer i {} {} t ty)
      List.foldr (fun (env_ty, ty') ty_acc => 
        let ty' := Ty.simplify ((Ty.subst env_ty (Ty.union ty' ty_acc)))
        Ty.generalize boundary env_ty ty'
        -- ty'
      ) Ty.bot u_env


    partial def infer_reduce (i : Nat) (t : Tm) : Ty := infer_reduce_wt (i + 1) t (Ty.fvar i)

    structure Work where
      cost : Nat
      i : Nat
      guides : PHashMap Nat Guide
      patches : PHashMap Nat Tm 
      t : Tm
    deriving Repr



    def Work.le (x y: Work): Bool := x.cost <= y.cost

    def Work.Queue := BinomialHeap Work Work.le

    partial def cost : Tm -> Nat
    | hole => 1 
    | .unit => 1 
    | bvar id => 1 
    | fvar id => 1
    | tag l t => 1 + (cost t)
    | record entries => 
      List.foldl (fun cost' (l, t) => cost' + (cost t)) 1 entries
    | func cases =>
      List.foldl (fun cost' (p, t_b) => cost' + (cost t_b)) 1 cases
    | proj t l => 1 + (cost t)
    | app t1 t2 => 1 + (cost t1) + (cost t2)
    | letb ty t1 t2 => 1 + (cost t1) + (cost t2)
    | .fix t => 1 + (cost t)

    partial def subst (m : PHashMap Nat Tm) : Tm -> Tm 
    | hole => hole 
    | .unit => .unit 
    | bvar id => bvar id 
    | fvar id => (match m.find? id with
      | some t => subst m t 
      | none => .fvar id
    )
    | tag l t => tag l (subst m t)
    | record entries => 
      let entries' := List.map (fun (l, t) => (l, subst m t)) entries 
      record entries'
    | func cases =>
      let cases' := List.map (fun (p, t_b) => 
        (p, subst m t_b)
      ) cases 
      func cases'
    | proj t l => proj (subst m t) l
    | app t1 t2 => app (subst m t1) (subst m t2)
    | letb ty t1 t2 => letb ty (subst m t1) (subst m t2)
    | .fix t => .fix (subst m t)

    -- (tag labels, field labels)
    partial def extract_labels : Ty -> (List String × List String)
    | .bvar id => ([], []) 
    | .fvar id => ([], [])
    | .unit => ([], []) 
    | .top => ([], [])
    | .bot => ([], [])
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


    partial def enumerate_fields : List String -> List (List (String × Tm))
    | [] => []
    | l :: ls =>
      (enumerate_fields ls).map (fun fields => (l, hole) :: fields)

    partial def enumerate_cases : List String -> List (List (Tm × Tm))
    | [] => []
    | l :: ls =>
      (enumerate_cases ls).map (fun cases => ([lessterm| #⟨l⟩ y[0] ], [lessterm| _ ]) :: cases)

    partial def join_functions (t1 : Tm) (t2 : Tm) : List Tm := match t1, t2 with
    | func cases1, func cases2 => [func (cases1 ++ cases2)]
    | _, _ => []

    partial def enumerate (i : Nat) (env_tm : PHashMap Nat Ty) (ty : Ty) : List Tm :=
      let (ls_t, ls_f) := (extract_labels ty)
      let tags := ls_t.map (fun l => tag l hole)

      let fields := enumerate_fields ls_f
      let records := fields.map (fun fds => record fds)

      let cases := enumerate_cases ls_t
      let functions := (
        [lessterm| \ y[0] => _ ] :: 
        (cases.map (fun cases => func cases))
      )

      [lessterm| () ] ::
      tags ++
      records ++
      functions ++
      [ [lessterm| let y[0] = _ in _ ] ] ++
      [ [lessterm| fix _ ] ] ++
      List.bind env_tm.toList (fun (x, ty) =>
        let (_, ls) := extract_labels ty
        let var := (fvar x)
        let application := [lessterm| let y[0] = (⟨fvar x⟩ _) in _ ] 
        let projections := ls.map (fun l =>
          [lessterm| let y[0] = (⟨fvar x⟩.⟨l⟩) in _ ] 
        )
        var :: application :: projections
      )

  end Tm


  -- #check BinomialHeap.ofList
  -- #check BinomialHeap.merge

  -- partial def synthesize_loop (queue : Work.Queue) : Option Tm := 
  --   Option.bind (queue.deleteMin) (fun (work, queue') =>
  --     if work.guides.isEmpty then
  --       some (Tm.subst work.patches work.t)
  --     else 
  --       let queue_ext := BinomialHeap.ofList Work.le (
  --         List.bind work.guides.toList (fun (id, guide) =>
  --           let hypotheses := enumerate work.i guide.env_tm guide.ty_expected
  --           List.bind hypotheses (fun h =>
  --           let contracts := (infer work.i {} guide.env_tm h guide.ty_expected)
  --           List.bind contracts (fun ⟨i, _, guides, t, _⟩ =>
  --             let patch := t
  --             [
  --               {
  --                 cost := work.cost + (Tm.cost h),
  --                 i := i,
  --                 guides := work.guides.erase id ; (PHashMap.from_list guides),
  --                 patches := work.patches.insert id patch 
  --                 t := work.t 
  --               }

  --             ]
  --           ))
  --         ) 
  --       )

  --       let queue'' := BinomialHeap.merge queue' queue_ext

  --       synthesize_loop queue''
  --   )



  -- partial def synthesize (t : Tm) : Option Tm := 
  --   let contracts := infer 0 {} {} t [lesstype| ∃ 1 => β[0] ]
  --   let works : List Work := contracts.map (fun contract =>
  --     {
  --       cost := (Tm.cost t), i := contract.i, 
  --       guides := PHashMap.from_list contract.guides, 
  --       patches := {},
  --       t := contract.t
  --     }
  --   )
  --   let queue := List.foldl (fun queue work =>
  --     queue.insert work
  --   ) BinomialHeap.empty works

  --   (synthesize_loop queue) 

  -- partial def synth_reduce (t : Tm) : Tm := 
  --   match synthesize t with
  --   | some t => t
  --   | none => Tm.hole


--------------------------------------------------
  open Ty Tm

  --- unification --
  def nat_ := [lesstype|
    induct 
      ?zero unit |
      ?succ β[0]
  ]

  
    
  #eval unify_simple 30
  [lesstype| (?zero unit) ] 
  [lesstype| ?zero unit | ?succ unit ]


  #eval unify_reduce 30
  [lesstype| (?succ ?succ ?succ α[0]) ] 
  [lesstype| ?zero unit | ?succ ⟨nat_⟩ ] 
  [lesstype| α[0] ]

  #eval unify_simple 30
  [lesstype| (?succ ?succ ?succ ?zero unit) ] 
  [lesstype| ?zero unit | ?succ ⟨nat_⟩ ]

  #eval unify_reduce 30
  [lesstype| (?succ α[0]) ] 
  nat_
  [lesstype| α[0] ]

  def nat_list := [lesstype| 
    induct 
      (?zero unit * ?nil unit) | 
      {?succ β[0] * ?cons β[1] with (β[0] * β[1]) <: β[2]}
  ]

  #eval unify_reduce 30
  [lesstype| (?succ ?zero unit) * ?cons α[0] ] 
  nat_list
  [lesstype| α[0] ]

  #eval unify_reduce 30
  [lesstype| ?succ ?zero unit * α[0] ]
  [lesstype| ⟨nat_list⟩ ]
  [lesstype| α[0] ]

  -- subtyping via local constraints
  #eval unify_reduce 30
  [lesstype| {β[0] with ?succ ?zero unit * β[0] <: ⟨nat_list⟩} ]
  [lesstype| ?cons α[0] ] 
  [lesstype| α[0] ]


  -- expected: ?cons ?nil unit
  #eval unify_reduce 30
  [lesstype| forall β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} ]
  [lesstype| ?succ ?succ ?zero unit -> ?cons α[0] ] 
  [lesstype| α[0] ]


  -- expected: ⊥
  #eval unify_reduce 30
  [lesstype| forall β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} ]
  [lesstype| ?foo ?succ ?zero unit -> α[0] ] 
  [lesstype| ?boo α[0] ]

  -----------------------------------------------

  def even_list := [lesstype| 
    induct 
      (?zero unit * ?nil unit) | 
      {?succ ?succ β[0] * ?cons ?cons β[1] with (β[0] * β[1]) <: β[2]}
  ]

  #eval unify_decide 0 even_list nat_list 
  #eval unify_decide 0 nat_list even_list

  def even := [lesstype| 
    induct ?zero unit | ?succ ?succ β[0]
  ]


  -- TODO: limitation: sound, but incomplete
  #eval unify_decide 0
  [lesstype| forall [1] β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} ]
  [lesstype| forall [1] β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} ]

  #eval unify_decide 0
  [lesstype| forall β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩}  ]
  [lesstype| forall β[0] <: ⟨even⟩ have β[0] -> {β[0] with β[1] * β[0] <: ⟨even_list⟩} ]


  #eval [lesstype| forall β[0] <: ⟨even⟩ have β[0] -> {β[0] with β[1] * β[0] <: ⟨even_list⟩} ]

  #eval unify_decide 0
  [lesstype| forall β[0] <: ⟨nat_⟩ have β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} ]
  [lesstype| forall β[0] <: ⟨even⟩ have β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} ]
  ----------------------------

  def plus := [lesstype| 
    induct 
      {x : ?zero unit & y : β[0] & z : β[0]} | 
      {x : ?succ β[0] & y : β[1] & z : ?succ β[2] with 
        (x : β[0] & y : β[1] & z : β[2]) <: β[3] 
      }
  ]

  #eval plus

  #eval unify_reduce 30 [lesstype|
    (
      x : (α[10]) &
      y : (?succ ?zero unit) & 
      z : (?succ ?succ ?zero unit)
    )
  ] plus
  [lesstype| α[10] ]

  #eval unify_reduce 30 
    [lesstype|
      (
        x : (?zero unit) &
        y : (?zero unit) & 
        z : (?zero unit)
      )
    ] 
    plus
    [lesstype| unit ]

  #eval unify_reduce 30 
    [lesstype|
      (
        x : (?succ ?zero unit) &
        y : (?succ ?succ ?zero unit) & 
        z : (?succ ?succ ?succ ?zero unit)
      )
    ] 
    plus
    [lesstype| unit ]


  #eval unify_reduce 30 [lesstype|
    (
      x : (?succ ?zero unit) & 
      y : (α[10]) &
      z : (?succ ?succ ?succ ?zero unit)
    )
  ] plus
  [lesstype| α[10] ]


  #eval unify_reduce 30 [lesstype|
    (
      x : ?succ α[1] &
      y : α[2] &
      z : (?succ ?succ ?zero unit)
    )
  ] plus
  [lesstype| α[1] * α[2] ]



  #eval unify_reduce 30 
  [lesstype| (α[0] * ?zero unit) | (?zero unit * α[0]) ] 
  [lesstype| (⟨nat_⟩ * ?zero unit) ] 
  [lesstype| α[0] ]



  #eval unify_reduce 30 [lesstype|
    (
      x : ?succ α[0] &
      y : α[2] &
      z : (?succ ?succ ?zero unit)
    )
  ] plus
  [lesstype| ?succ α[0] * α[2] ]

  #eval unify_reduce 30 [lesstype|
    (
      x : α[0] &
      y : α[2] &
      z : (?succ ?succ ?zero unit)
    )
  ] plus
  [lesstype| α[0] * α[2] ]

  #eval unify_reduce 1 [lesstype|
    (
      x : (?succ ?succ ?zero unit) & 
      y : (?succ ?zero unit) &
      z : (α[0])
    )
  ] plus
  [lesstype| α[0] ]
  -- == [lesstype| ?succ ?succ ?succ ?zero unit ]

  #eval unify_reduce 30 [lesstype|
    (
      x : (?succ ?zero unit) & 
      y : (α[10]) &
      z : (?succ ?succ ?zero unit)
    )
  ] plus
  [lesstype| α[10] ]


  #eval unify_reduce 10 [lesstype|
  (
    x : α[5] &
    y : ?succ ?zero unit &
    z : ?succ ?succ ?zero unit
  )
  ] plus
  [lesstype| α[5] ]

  #eval unify_simple 10 
    [lesstype| ⊥ ] 
    plus 

  #eval unify_simple 10 
    plus 
    [lesstype| ⊥ ] 

  ------ type inference --------
  #eval infer_reduce 0 [lessterm|
    #succ #zero ()
  ]

  -- expected: ?cons ?nil unit
  #eval infer_reduce 0 [lessterm|
    let y[0] : forall β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} = _ in 
    (y[0] (#succ #zero ()))
  ]



  #eval[lessterm|
    \ y[0] => 
      \ #zero () => #nil ()
      \ #succ y[0] => #cons (y[1] y[0])
  ]

  #eval[lessterm|
    \ y[0] => (
      \ #zero () => #nil ()
      \ #succ y[0] => #cons (y[1] y[0])
    )
  ]

  #eval infer_reduce 0 [lessterm|
    fix(\ y[0] => (
    \ #zero () => #nil ()
    \ #succ y[0] => #cons (y[1] y[0])
    )
    )
  ]

  #eval infer_reduce 0 [lessterm|
    let y[0] = fix(\ y[0] => 
      \ #zero () => #nil (),
      \ #succ y[0] => #cons (y[1] y[0])
    ) in 
    y[0]
  ]

  -- expected: ?cons ?nil unit
  #eval infer_reduce 10 [lessterm|
    let y[0] = fix(\ y[0] => ( 
      \ #zero () => #nil (),
      \ #succ y[0] => #cons (y[1] y[0])
    )) in 
    (y[0] (#succ #zero ()))
  ]


  -- expected: ?cons ?nil unit
  #eval infer_reduce 0 [lessterm|
    let y[0] : (?zero unit -> ?nil unit) & (?succ ?zero unit -> ?cons ?nil unit) = _ in 
    (y[0] (#succ #zero ()))
  ]


  ---------- generics ----------------

  #eval infer_reduce 10 [lessterm|
    ((\ #cons (y[0], y[1]) => y[0]) (#cons (#ooga (), #booga ())))
  ]

  #eval infer_reduce 10 [lessterm|
    let y[0] = (\ #cons (y[0], y[1]) => y[0]) in
    (y[0] (#cons (#ooga (), #booga ())))  
  ]

  #eval infer_reduce 10 [lessterm|
    let y[0] = (\ #cons (y[0], y[1]) => y[0]) in 
    y[0]  
  ]

  #eval infer_reduce 10 [lessterm|
    let y[0] : forall ?cons (β[0] * β[1]) -> β[0] = _ in
    (y[0] (#cons (#ooga (), #booga ())))  
  ]

  ---------- adjustment ----------------

  -- widening
  #eval infer_reduce 0 [lessterm|
    let y[0] : forall β[0] -> (β[0] -> (β[0] * β[0])) = _ in 
    ((y[0] #hello ()) #world ())
  ]

  #eval infer_reduce 0 [lessterm|
    let y[0] : forall β[0] -> (β[0] -> (β[0] * β[0])) = _ in 
    (y[0] #hello ())
  ]

  #eval infer_reduce 0 [lessterm|
    let y[0] : forall β[0] -> (β[0] -> (β[0] * β[0])) = _ in 
    let y[0] = (y[0] #hello ()) in
    (y[0] #world ())
  ]

  -- narrowing
  #eval infer_reduce 0 [lessterm|
  let y[0] : ?uno unit -> unit = _ in 
  let y[0] : ?dos unit -> unit = _ in 
  (\ y[0] =>
    ((y[2] y[0]), (y[1] y[0])))
  ]

  #eval infer_reduce 0 [lessterm|
  let y[0] : ?uno unit -> unit = _ in 
  let y[0] : ?dos unit -> unit = _ in 
  (\ y[0] =>
    let y[0] = (y[2] y[0]) in 
    let y[0] = (y[2] y[1]) in 
    (y[0], y[1]))
  ]

  ----------------------------------
  #eval [lessterm| @x = #hello () @y = #world ()]
  --------------------------------------

  #eval unify_decide 0 
    [lesstype| ?hello unit ] 
    [lesstype| α[0] ] 

  -- not well foundend: induction untagged 
  #eval unify_decide 0 
    [lesstype| ?hello unit ] 
    [lesstype| induct ?wrong unit | β[0] ] 

  -- potentially diverges - inductive type not well founded
  #eval unify_decide 0 
    [lesstype| ?hello unit ] 
    [lesstype| induct β[0] ] 

  def bad_nat_list := [lesstype| 
    induct 
      (?zero unit * ?nil unit) | 
      {(β[0] * β[1]) with β[0] * β[1] <: β[2]}
  ]

  #eval unify_decide 0 
    [lesstype| ?zero unit * ?nil unit ] 
    bad_nat_list

  def other_nat_list := [lesstype| 
    induct {(?succ β[0] * ?cons β[1]) with β[0] * β[1] <: β[2]}
  ]

  -- expected: false; base case is missing
  #eval unify_decide 0 
    [lesstype| ?succ ?zero unit * ?cons ?nil unit ] 
    other_nat_list

  #eval [lessterm|
  (\ y[0] => ( 
    \ (#succ y[0], #succ y[1]) => (y[2] (y[0], y[1]))
    \ (#zero (), y[0]) => y[0]
    \ (y[0], #zero ()) => y[0] 
  ))
  ]

  #eval infer_reduce 10 [lessterm|
  fix(\ y[0] => ( 
    \ (#succ y[0], #succ y[1]) => (y[2] (y[0], y[1]))
    \ (#zero (), y[0]) => y[0]
    \ (y[0], #zero ()) => y[0] 
  ))
  ]

  -- expected: ?succ ?zero unit
  #eval infer_reduce 10 [lessterm|
  (fix(\ y[0] => ( 
    \ (#succ y[0], #succ y[1]) => (y[2] (y[0], y[1]))
    \ (#zero (), y[0]) => y[0]
    \ (y[0], #zero ()) => y[0] 
  )) (#succ #succ #zero (), #succ #succ #succ #zero ()))
  ]

  ----------------------------------

  def gt := [lesstype| 
    induct  
      {?succ β[0] * ?zero unit} | 
      {?succ β[0] * ?succ β[1] with (β[0] * β[1]) <: β[2]}
  ]

  -------------------------------------------------

  def spec := [lesstype| 
  (α[0] * α[1]) -> (
    { β[0] with (x:β[0] & y:α[1] & z:α[0]) <: ⟨plus⟩} |
    { β[0] with (x:β[0] & y:α[0] & z:α[1]) <: ⟨plus⟩}
  )  
  ]

  -- Note: is this in effect, the same thing as PDR/IC3
  -- That is, whatever is learned to strengthen the premise 
  -- is automatically applied to preceding iterations 
  -- due to the wrapping type with the co-inductive nu binder
  -- TODO
  #eval infer_reduce 10 
  [lessterm|
  let y[0] : ⟨spec⟩ = fix(\ y[0] => ( 
    \ (#succ y[0], #succ y[1]) => (y[2] (y[0], y[1]))
    \ (#zero (), y[0]) => y[0]
    \ (y[0], #zero ()) => y[0] 
  )) in 
  y[0]
  ]

  #eval infer_reduce 10 
  [lessterm|
  let y[0] = fix(\ y[0] => ( 
    \ (#succ y[0], #succ y[1]) => (y[2] (y[0], y[1]))
    \ (#zero (), y[0]) => y[0]
    \ (y[0], #zero ()) => y[0] 
  )) in 
  y[0]
  ]

  #eval infer_reduce 10 
  [lessterm|
  let y[0] = fix(\ y[0] => ( 
    \ (#succ y[0], #succ y[1]) => (y[2] (y[0], y[1]))
    \ (#zero (), y[0]) => y[0]
    \ (y[0], #zero ()) => y[0] 
  )) in 
  (y[0] (#succ #succ #zero (), #succ #zero ()))
  ]

  def diff_rel :=
  [lesstype|
    induct 
      {?zero unit * β[0] * β[0]} | 
      {β[0] * ?zero unit * β[0]} |
      {(?succ β[1] * ?succ β[2] * β[0]) with (β[1] * β[2] * β[0]) <: β[3]}
  ]

  #eval unify_reduce 10
  [lesstype| ?succ ?succ ?zero unit * ?succ ?zero unit * α[0] ]
  diff_rel
  [lesstype| α[0] ]



  def plus_choice := [lesstype| 
  α[0] * α[1] * (
    { β[0] with (x:β[0] & y:α[1] & z:α[0]) <: ⟨plus⟩} |
    { β[0] with (x:β[0] & y:α[0] & z:α[1]) <: ⟨plus⟩}
  )  
  ]

  #eval unify_reduce 10
  plus_choice
  diff_rel
  [lesstype| α[0] ]


  #eval unify_reduce 10
  [lesstype|
  forall β[0] -> {β[0] with (β[1] * β[0]) <: ⟨diff_rel⟩}
  ]
  spec
  [lesstype| α[0] * α[1] ]
  --------------------------------------


  -- #eval rewrite_function_type diff


  #eval infer_reduce 10 
  [lessterm|
  let y[0] : (
    (forall (?hello β[0] -> ?world unit)) & 
    (forall ?one β[0] -> ?two unit)
  ) = _ in 
  (y[0] #one ())
  ]

  #eval infer_reduce 10 
  [lessterm|
  let y[0] : (
    (forall 
      (?hello β[0] -> ?world unit) & 
      (?one β[0] -> ?two unit)
    )
  ) = _ in 
  (y[0] #one ())
  ]

  -- def even_to_list := [lesstype| 
  --   ν 1 . (
  --     (?zero unit -> ?nil unit) & 
  --     (∀ 2 . (?succ ?succ β[0] -> ?cons ?cons β[1]) | 
  --       β[2] ≤ β[0] -> β[1])
  --   )
  -- ]

  -- #eval unify_decide 0 
  --   even_to_list
  --   nat_to_list
  -- -- == false 

  -- -- TODO
  -- #eval unify_decide 0 
  --   nat_to_list
  --   even_to_list
  -- -- == true

  -- #eval unify_decide 0 
  -- [lesstype| ∃ 1 .  β[0] ]
  -- [lesstype| ∃ 1 .  ?cons unit ]
  -- -- == false 

  -- #eval unify_decide 0 
  -- [lesstype| ∃ 1 .  ?cons unit ]
  -- [lesstype| ∃ 1 .  β[0] ]
  -- -- == true 

  -- #eval unify_decide 0 
  -- [lesstype| ∀ 1 .  β[0] ]
  -- [lesstype| ∀ 1 .  ?cons unit ]
  -- -- == true 

  -- #eval unify_decide 0 
  -- [lesstype| ∀ 1 .  ?cons unit ]
  -- [lesstype| ∀ 1 .  β[0] ]
  -- -- == false 


  -- #eval unify_decide 0 
  -- [lesstype| ∃ 1 . (?succ ?succ unit) ]
  -- [lesstype| ∃ 1 . (?succ ?succ β[0]) ]

  -- #eval unify_decide 0 
  -- [lesstype| ∀ 2 . (?succ ?succ β[0] -> ?cons ?cons β[1]) ]
  -- [lesstype| ∀ 2 . (?succ ?succ unit -> ?cons ?cons unit) ]




  -- -- def nat_to_list := [lesstype| 
  -- --   ν 1 . (
  -- --     (?zero unit -> ?nil unit) & 
  -- --     (∀ 2 . (?succ β[0] -> ?cons β[1]) | 
  -- --       β[2] ≤ β[0] -> β[1])
  -- --   )
  -- -- ]


  -- -- def even_to_list := [lesstype| 
  -- --   ν 1 . (
  -- --     (?zero unit -> ?nil unit) & 
  -- --     (∀ 2 . (?succ ?succ β[0] -> ?cons ?cons β[1]) | 
  -- --       β[2] ≤ β[0] -> β[1])
  -- --   )
  -- -- ]


end Nameless 


    --------------------- OLD STUFF -------------------------------------
    -- | ty1, .univ n ty_c1 ty_c2 ty2 =>
    --   let bound_start := i
    --   let (i, ids) := (i + n, (List.range n).map (fun j => i + j))
    --   let bound_end := i
    --   let is_bound_var := (fun i' => bound_start <= i' && i' < bound_end)

    --   let args := ids.map (fun id => Ty.fvar id)
    --   let ty_c1 := Ty.instantiate 0 args ty_c1
    --   let ty_c2 := Ty.instantiate 0 args ty_c2
    --   let ty2 := Ty.instantiate 0 args ty2

    --   let op_fields := linearize_fields ty_c2

    --   let ((i, contexts), env_complex) := ( 
    --     match op_fields with 
    --     | some fields =>
    --       let is_corec_type := match ty_c1 with 
    --       | Ty.corec _ => true
    --       | _ => false
    --       let is_consistent_variable_record := List.all fields (fun (l, ty_fd) =>
    --         let rlabels := extract_record_labels (ty_c1) 
    --         rlabels.contains l &&
    --         (match ty_fd with | (Ty.fvar _) => true | _ => false)
    --       )
    --       if is_corec_type && is_consistent_variable_record then
    --         let ty_norm := ty_c2
    --         ((i, [env_ty]), env_complex.insert (.up, ty_norm) ty_c1)

    --       else ((i, []), env_complex) 
    --     | none => (unify i (env_ty) env_complex frozen ty_c1 ty_c2, env_complex)
    --   )

    --   -- vacuous truth unsafe: given P |- Q, if P is incorreclty false, then P |- Q is incorrecly true (which is unsound)
    --   assume_env (i, contexts) (fun i env_ty => 
    --   assume_env (unify i env_ty env_complex frozen ty1 ty2) (fun i env_ty => 
    --     let is_result_safe := List.all env_ty.toList (fun (key, ty_value) =>
    --       not (is_bound_var key) 
    --     )
    --     if is_result_safe then
    --       (i, [env_ty])
    --     else
    --       (i, [])
    --   ))

    -- | .case ty1 ty2, .case ty3 ty4 =>

    --   let n1 := infer_abstraction ty1 
    --   let n3 := infer_abstraction ty3 
    --   if n1 == 0 && n3 == 0 then 
    --     assume_env (unify i env_ty env_complex frozen ty3 ty1) (fun i env_ty =>
    --       (unify i env_ty env_complex frozen ty2 ty4)
    --     ) 
    --   else if n1 >= n3 then
    --     let (i, ids1) := (i + n1, (List.range n1).map (fun j => i + j))
    --     let args1 := ids1.map (fun id => Ty.fvar id)
    --     let ty1' := Ty.instantiate 0 args1 ty1
    --     let ty2' := Ty.instantiate 0 args1 ty2

    --     let (i, ids3) := (i + n3, (List.range n3).map (fun j => i + j))
    --     let is_opaque := fun key => ids3.contains key 
    --     let args3 := ids3.map (fun id => Ty.fvar id)
    --     let ty3' := Ty.instantiate 0 args3 ty3
    --     let ty4' := Ty.instantiate 0 args3 ty4

    --     assume_env (unify i env_ty env_complex frozen ty3' ty1') (fun i env_ty =>
    --       let is_result_safe := List.all env_ty.toList (fun (key, ty_value) =>
    --         not (is_opaque key)
    --       )
    --       if is_result_safe then
    --         (unify i env_ty env_complex frozen ty2' ty4')
    --       else
    --         (i, [])
    --     ) 
    --   else 
    --     (i, [])
    -----------------------------------------------------------------------


  -- def unify_all (i : Nat) (cs : List (Ty × Ty)) : (Nat × List (PHashMap Ty Ty)) := 
  --   List.foldl (fun u_env_ty1 => fun (ty_c1, ty_c2) => 
  --     Option.bind u_env_ty1 (fun (i, env_ty1) => 
  --     Option.bind (Ty.unify i env_ty1 ty_c1 ty_c2) (fun (i, env_ty2) =>
  --       some (i, env_ty1 ; env_ty2)
  --     ))
  --   ) (some (i, {})) cs


  -- def Ty.refresh (i : Nat) : Ty -> (Nat × Ty)
  --   | .bvar id => (i + 1, Ty.bvar id) 
  --   | .fvar _ => (i + 1, Ty.fvar i)
  --   | .unit => (i + 1, .unit) 
  --   | .bot => (i + 1, .bot) 
  --   | .top => (i + 1, .top) 
  --   | .tag l ty => 
  --     let (i, ty) := Ty.refresh i ty 
  --     (i, Ty.tag l ty) 
  --   | .field l ty => 
  --     let (i, ty) := Ty.refresh i ty 
  --     (i, Ty.field l ty) 
  --   | .union ty1 ty2 => 
  --     let (i, ty1) := Ty.refresh i ty1
  --     let (i, ty2) := Ty.refresh i ty2
  --     (i, .union ty1 ty2)
  --   | .inter ty1 ty2 => 
  --     let (i, ty1) := Ty.refresh i ty1
  --     let (i, ty2) := Ty.refresh i ty2
  --     (i, .inter ty1 ty2)
  --   | .case ty1 ty2 => 
  --     let (i, ty1) := Ty.refresh i ty1
  --     let (i, ty2) := Ty.refresh i ty2
  --     (i, .case ty1 ty2)
  --   | .univ n cty1 cty2 ty => 
  --     let (i, cty1) := Ty.refresh i cty1
  --     let (i, cty2) := Ty.refresh i cty2
  --     let (i, ty) := Ty.refresh i ty
  --     (i, .univ n cty1 cty2 ty)
  --   | .exis n cty1 cty2 ty => 
  --     let (i, cty1) := Ty.refresh i cty1
  --     let (i, cty2) := Ty.refresh i cty2
  --     let (i, ty) := Ty.refresh i ty
  --     (i, .exis n cty1 cty2 ty)
  --   | .recur ty =>
  --     let (i, ty) := Ty.refresh i ty
  --     (i, .recur ty)
  --   | .corec ty =>
  --     let (i, ty) := Ty.refresh i ty
  --     (i, .corec ty)

/- OLD: don't think normal form is relevant here
  -- TODO: create non-normal types with encoding/decoding to normal types 
    -- non-normal has named variable binding

  -- TODO?: normalize record intersection as Map from fields to type 
  -- TODO?: normalize function intersection as Map from type to type 
    -- requires notion of intersectable.
    -- if adding field to intersection of fields 
    -- if adding function to function or intersectino of functions
  -- TODO?: normalize union as set of types   
    -- requires notion of unionable.
  -- Normal form of types uses De Bruijn indexing for bound type variables
  -- TODO: Normal form of types using De Bruijn indexing for bound type variables
  -- TODO: convert top and bottom into sugar: ⊤ = ∃ α . α, ⊥  = ∀ α . α
  -- TODO: remove top and bottom types 
-/


  -- def intersect_fields : List (String × Ty) -> Ty
  -- | [] => [lesstype| {β[0]} ] 
  -- | (l, ty) :: fields => Ty.inter (Ty.field l ty) (intersect_fields fields)

  -- def normalize_fields (fields : List (String × Ty)) : List (String × Ty) :=
  --   mergeSort (fun (l1, _) (l2, _) => l1 < l2) fields

  -- -- α[0] ↦ ∃ β[0] :: β[0] × α[1] ≤ ⟨nat_list⟩ => β[0]   
  -- -- succ * α[2] ≤ ∃ β[0] :: β[0] × α[1] ≤ ⟨nat_list⟩ => β[0]   
  -- def separate_fields (prev_fields var_fields : List (String × Ty)) (ty_rhs : Ty) : PHashMap Nat Ty :=
  -- match var_fields with
  -- | [] => {}
  -- | (l, ty_fd) :: var_fields' =>
  --   match ty_fd with
  --   | Ty.fvar id =>
  --     let fields := 
  --       prev_fields ++ (l, [lesstype| β[0] ]) :: var_fields 
  --     let ty_lhs := intersect_fields fields
  --     let ty := [lesstype| {[1] β[0] with ⟨ty_lhs⟩ <: ⟨ty_rhs⟩} ]
  --     let m : PHashMap Nat Ty := (separate_fields (prev_fields ++ [(l, ty_fd)]) var_fields') ty_rhs
  --     m.insert id ty
  --   | _ => {}



  -- def wellformed_record_type (env_ty : PHashMap Nat Ty) (ty : Ty) : Bool :=
  --   match linearize_fields (Ty.simplify (Ty.subst env_ty ty)) with
  --   | .some fields => 
  --     List.any fields (fun (k_fd, ty_fd) =>
  --       match ty_fd with
  --       | .fvar _ => false 
  --       | _ => true 
  --     ) 
  --   | .none => false

  -- partial def wellformed_unroll_type (env_ty : PHashMap Nat Ty) (ty : Ty) : Bool :=
  --   match (Ty.simplify (Ty.subst env_ty ty)) with 
  --   | .fvar _ => false
  --   | ty => (linearize_fields ty == .none) || (wellformed_record_type env_ty ty)


  -- def extract_premise (start : Nat) : Ty -> Option Ty 
  -- | .univ n [lesstype| unit ] [lesstype| unit ] ty3 => 
  --   Option.bind (extract_premise (start + n) ty3) (fun ty3_prem =>
  --     (Ty.exis n [lesstype| unit ] [lesstype| unit ] ty3_prem)
  --   )
  -- | .univ n (.bvar id) ty0  ty3 => 
  --   if id == start + n then
  --     Option.bind (extract_premise (start + n) ty0) (fun ty0_prem => 
  --     Option.bind (extract_premise (start + n) ty3) (fun ty3_prem =>
  --       (Ty.exis n ty0_prem (.bvar (start + n)) ty3_prem)
  --     ))
  --   else 
  --     none
  -- | Ty.inter ty1 Ty.top => 
  --   (extract_premise start ty1)
  -- | Ty.inter ty1 (Ty.fvar _) => 
  --   (extract_premise start ty1)
  -- | Ty.inter Ty.top ty2 => 
  --   (extract_premise start ty2)
  -- | Ty.inter (Ty.fvar _) ty2 => 
  --   (extract_premise start ty2)
  -- | Ty.inter ty1 ty2 => 
  --   Option.bind (extract_premise start ty1) (fun ty1_prem =>
  --   Option.bind (extract_premise start ty2) (fun ty2_prem =>
  --     Ty.union ty1_prem ty2_prem
  --   ))
  -- | Ty.case ty1 _ => some ty1 
  -- | _ => none

  -- def extract_relation (start : Nat) : Ty -> Option Ty 
  -- -- TODO: convert universal to arrow type with variable parameter type
  -- | .univ n [lesstype| unit ] [lesstype| unit ] ty3 => 
  --   Option.bind (extract_relation (start + n) ty3) (fun ty3_rel =>
  --     (Ty.exis n [lesstype| unit ] [lesstype| unit ] ty3_rel)
  --   )
  -- | .univ n (.bvar id) ty0 ty3 => 
  --   if id == start + n then
  --     Option.bind (extract_relation (start + n) ty0) (fun ty0_rel =>
  --     Option.bind (extract_relation (start + n) ty3) (fun ty3_rel =>
  --       (Ty.exis n ty0_rel (.bvar (start + n)) ty3_rel)
  --     ))
  --   else 
  --     none
  -- | Ty.inter ty1 Ty.top => 
  --   (extract_relation start ty1)
  -- | Ty.inter ty1 (Ty.fvar _) => 
  --   (extract_relation start ty1)
  -- | Ty.inter Ty.top ty2 => 
  --   (extract_relation start ty2)
  -- | Ty.inter (Ty.fvar _) ty2 => 
  --   (extract_relation start ty2)
  -- | Ty.inter ty1 ty2 => 
  --   Option.bind (extract_relation start ty1) (fun ty1_rel =>
  --   Option.bind (extract_relation start ty2) (fun ty2_rel =>
  --     Ty.union ty1_rel ty2_rel
  --   ))
  -- | Ty.case ty1 ty2 => 
  --   some [lesstype| ⟨ty1⟩ × ⟨ty2⟩ ] 
  -- | _ => none


  -- def rewrite_corec (ty : Ty) : Option Ty  :=
  --   bind (extract_relation 0 ty) (fun rel =>
  --     [lesstype|
  --       (
  --         β[0] -> (∃ 1 . β[0] | β[1] × β[0] ≤ ⟨Ty.recur rel⟩)
  --       ) 
  --     ]
  --   )
  --   -- bind (extract_premise 0 ty) (fun prem =>
  --       -- | β[0] ≤ ⟨Ty.recur prem⟩
  --     -- [lesstype|
  --     --   ∀ 1 . (
  --     --     β[0] -> (∃ 1 . β[0] | β[1] × β[0] ≤ ⟨Ty.recur rel⟩)
  --     --   ) | β[0] ≤ ⟨Ty.recur prem⟩
  --     -- ]
  --   -- )


  -- def linearize_record : Ty -> Option Ty
  -- | .field l ty => 
  --   some (.field l ty)
  -- | .inter (.field l ty1) ty2 => 
  --   bind (linearize_record ty2) (fun linear_ty2 =>
  --     some (.inter (.field l ty1) linear_ty2)
  --   )
  -- | .inter ty1 (.field l ty2) => 
  --   bind (linearize_record ty1) (fun linear_ty1 =>
  --     some (.inter (.field l ty2) linear_ty1)
  --   )
  -- | _ => none

/- old stuff
      -- let ty' := Ty.generalize 0 env_ty ty'
      -- Ty.simplify ((Ty.subst env_ty (Ty.union ty' ty_acc)))
      -- let pos_neg_set := PHashMap.intersect (Ty.signed_free_vars true ty') (Ty.signed_free_vars false ty')

      -- let fvs := pos_neg_set.toList.reverse.bind (fun (k, _) => [k])
      -- if fvs.isEmpty then
      --   Ty.simplify (Ty.subst_default true ty')
      -- else
      --   Ty.simplify (Ty.subst_default true (Ty.abstract fvs 0 ty'))
-/


-----------------------------------------------
  ---- debugging
  -- TODO: fix subtype unification

  def nat_ := [lesstype|
    induct 
      ?zero unit |
      ?succ β[0]
  ]

  def list_ := [lesstype|
    induct 
      ?nil unit |
      ?cons β[0]
  ]

  def nat_list := [lesstype|
    induct 
      (?zero unit * ?nil unit) |
      {?succ β[0] * ?cons β[1] with β[0] * β[1] <: β[2]}
  ]

  #eval [lessterm| 
    let y[0] : ⟨nat_⟩ -> ⟨list_⟩ = fix(\ y[0] =>
      \ #zero() => #nil()  
      \ #succ y[0] => #cons (y[1] y[0]) 
    )
    in
    y[0]
  ] 

  #eval Nameless.Tm.infer_reduce 0 [lessterm| 
    fix(\ y[0] =>
      \ #zero() => #nil()  
      \ #succ y[0] => #cons (y[1] y[0]) 
    )
  ]


  ------------ transpose_relation ----------------

  def nat_list_trans := Nameless.Ty.transpose_relation ["l", "r"] nat_list
  #eval nat_list_trans

  #eval Nameless.Ty.unify_decide 0
  [lesstype| {β[0] with β[0] * α[0] <: ⟨nat_list_trans⟩} ]
  [lesstype| ⟨nat_⟩ ]

  #eval Nameless.Ty.unify_decide 0
  [lesstype| {β[0] with β[0] * α[0] <: ⟨nat_list⟩} ]
  [lesstype| ⟨nat_⟩ ]

  #eval Nameless.Ty.unify_decide 0
  [lesstype| forall β[0] <: ⟨nat_⟩ have β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} ]
  [lesstype| ⟨nat_⟩ -> ⟨list_⟩ ]

---------------- debugging

  #eval Nameless.Tm.infer_reduce 0 [lessterm| 
    let y[0] : ⟨nat_⟩ -> ⟨list_⟩ = fix(\ y[0] =>
      \ #zero() => #nil()  
      \ #succ y[0] => #cons (y[1] y[0]) 
    )
    in
    y[0]
  ] 
  --------------------------------