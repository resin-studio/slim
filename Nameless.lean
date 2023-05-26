import Std.Data.BinomialHeap
import Init.Data.Hashable
import Lean.Data.PersistentHashMap
import Lean.Data.PersistentHashSet

import Util

open Lean PersistentHashMap PersistentHashSet
open Std
-- open Lean PHashMap PHashSet

open PHashSet


partial def multi_step {T : Type} [BEq T] (step : T -> T) (source : T): T :=
  let sink := step source 
  if sink == source then
    sink
  else 
    multi_step step sink

namespace Nameless 

  def bind_nl (i_xs : Nat × List α) 
  (f : Nat -> α -> (Nat × List β)) :
  (Nat × List β) :=
    let (i, xs) := i_xs
    List.foldl (fun (i, u_acc) env_ty =>
      let (i, xs) := (f i env_ty)
      (i, u_acc ++ xs)
    ) (i, []) xs 

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

    structure Context where
      env_simple : PHashMap Nat Ty
      env_relational : PHashMap Ty Ty
      set_expandable : PHashSet Nat
    deriving Repr


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
    | .exis n ty_c1 ty_c2 ty_pl =>
      let n_c1 := infer_abstraction (start + n) ty_c1 
      let n_c2 := infer_abstraction (start + n) ty_c2
      let n_pl := infer_abstraction (start + n) ty_pl  
      Nat.max (Nat.max n_c1 n_c2) n_pl
    | .univ n ty_c1 ty_c2 ty_pl =>
      let n_c1 := infer_abstraction (start + n) ty_c1 
      let n_c2 := infer_abstraction (start + n) ty_c2
      let n_pl := infer_abstraction (start + n) ty_pl  
      Nat.max (Nat.max n_c1 n_c2) n_pl
    | .recur content =>
      infer_abstraction (start + 1) content 

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
    | ty1, .inter ty21 ty22 => 
      inter_contains ty1 ty21 ||
      inter_contains ty1 ty22
    | ty1, ty2 => ty1 == ty2

    -- make assoc right
    partial def intersect : Ty -> Ty -> Ty
    | .top, ty2 => ty2 
    | .unit, .tag _ _ => Ty.bot 
    | .tag _ _, .unit  => Ty.bot 
    | .tag l1 ty1, .tag l2 ty2  => 
      if l1 != l2 then
        Ty.bot 
      else
        .tag l1 (intersect ty1 ty2)
    | .tag l1 ty1, Ty.union ty21 ty22  => 
      Ty.union 
        (intersect (.tag l1 ty1) ty21) 
        (intersect (.tag l1 ty1) ty22)

    | Ty.union ty21 ty22, .tag l1 ty1 => 
      Ty.union 
        (intersect (.tag l1 ty1) ty21) 
        (intersect (.tag l1 ty1) ty22)

    | .bot, _ => .bot 
    | .inter ty11 ty12, ty2 => intersect ty11 (intersect ty12 ty2) 
    | ty1, .top => ty1 
    | _, .bot => .bot 
    | ty1, ty2 => 
        if ty1 == ty2 then
          ty1
        else if inter_contains ty1 ty2 then
          ty1
        else if inter_contains ty2 ty1 then
          ty2
        else
          .inter ty1 ty2


    -- assume assoc right
    def union_contains : Ty -> Ty -> Bool 
    | ty1, .union ty21 ty22 => 
      union_contains ty1 ty21 ||
      union_contains ty1 ty22
    | ty1, ty2 => ty1 == ty2

    -- make assoc right
    def unionize : Ty -> Ty -> Ty
    | .top, _ => .top
    | .bot, ty2 => ty2
    | .union ty11 ty12, ty2 => unionize ty11 (unionize ty12 ty2) 
    | _, .top => .top 
    | ty1, .bot => ty1
    | ty1, ty2 => 
        if ty1 == ty2 then
          ty1
        else if union_contains ty1 ty2 then
          ty1
        else if union_contains ty2 ty1 then
          ty2
        else
          .union ty1 ty2

    partial def simplify : Ty -> Ty
    | .bvar id => .bvar id  
    | .fvar id => .fvar id
    | .unit => .unit 
    | .top => .top
    | .bot => .bot 
    | .tag l ty => .tag l (simplify ty) 
    | .field l ty => .field l (simplify ty) 
    | .union ty1 ty2 => unionize (simplify ty1) (simplify ty2)
    | .inter ty1 ty2 => intersect (simplify ty1) (simplify ty2)
    | .case ty1 ty2 => .case (simplify ty1) (simplify ty2)
    | .exis n cty1 cty2 ty => 
      .exis n (simplify cty1) (simplify cty2) (simplify ty)
    | .univ n cty1 cty2 ty => 
      .univ n (simplify cty1) (simplify cty2) (simplify ty)
    | .recur ty => .recur (simplify ty)


    def intersect_over (f : (Ty × Ty) -> Ty) (constraints : List (Ty × Ty)) : Ty :=
      (constraints.foldr (fun (lhs, rhs) ty_acc =>
        intersect (f (lhs, rhs)) ty_acc 
      ) Ty.top)

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


    -- constraints
    syntax:40 lesstype "<:" lesstype : lesstype
    syntax:40 lesstype "<:" lesstype "," lesstype: lesstype
    ------------


    syntax "{" "[" lesstype "]" lesstype:41 "with" lesstype "}": lesstype 
    syntax "{" "[" lesstype "]" lesstype:41 "}" : lesstype 

    syntax "{" lesstype:41 "with" lesstype "}": lesstype 
    syntax "{" lesstype:41 "}" : lesstype 

    syntax "forall" "[" lesstype "]" lesstype "have" lesstype:41 : lesstype 
    syntax "forall" "[" lesstype "]" lesstype:41 : lesstype 

    syntax "forall" lesstype "have" lesstype:41 : lesstype 
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


    -- constraints
    | `([lesstype| $b <: $c  ]) => `([([lesstype| $b ],[lesstype| $c ])])
    | `([lesstype| $b <: $c , $xs ]) => `(([lesstype| $b ],[lesstype| $c ]) :: [lesstype| $xs])
    --------------

    | `([lesstype| { [$n] $d with $xs }  ]) => 
      `(intersect_over (fun (lhs, rhs) => Ty.exis [lesstype| $n ] lhs rhs [lesstype| $d ]) [lesstype| $xs ])

    | `([lesstype| { [$n] $b:lesstype } ]) => `(Ty.exis [lesstype| $n ] Ty.unit Ty.unit [lesstype| $b ] )

    | `([lesstype| { $d with $xs}  ]) => 
      `(intersect_over 
        (fun (lhs, rhs) => Ty.exis (Ty.infer_abstraction 0 [lesstype| $d ]) lhs rhs [lesstype| $d ])
        [lesstype| $xs]
      )

    | `([lesstype| { $b:lesstype } ]) => 
      `(Ty.exis (Ty.infer_abstraction 0 [lesstype| $b ]) Ty.unit Ty.unit [lesstype| $b ] )

    | `([lesstype| forall $xs have $d  ]) => 
      `(intersect_over 
        (fun (lhs, rhs) => Ty.univ (Ty.infer_abstraction 0 [lesstype| $d ]) lhs rhs [lesstype| $d ])
        [lesstype| $xs]
      )

    | `([lesstype| forall $b:lesstype  ]) => 
      `(Ty.univ (Ty.infer_abstraction 0 [lesstype| $b ]) Ty.unit Ty.unit [lesstype| $b ] )

    | `([lesstype| forall [$n] $xs have $d  ]) => 
      `(intersect_over
        (fun (lhs, rhs) => Ty.univ [lesstype| $n ] lhs rhs [lesstype| $d ])
        [lesstype| $xs ]
      )

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
  
    | .inter (.field "l" l) (.field "r" r) =>
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


    def reduce (env_ty : PHashMap Nat Ty) (ty : Ty) :=
      (simplify (subst (env_ty) ty))


------------------------------------------------------------

    #eval [lesstype| {β[0] with β[0] <: ?ooga unit, β[0] <: ?booga unit} ]
    #eval [lesstype| {β[0] with β[0] <: ?ooga unit} ]

    #eval [lesstype| {[1] β[0] with (β[1] * β[0]) <: ?booga unit} ] 
    #eval [lesstype| {[1] β[0] with β[1] * β[0] <: ?booga unit} ] 
    #eval [lesstype| forall [1] β[0] <: ?ooga unit have β[0] -> {[1] β[0] with β[1] * β[0] <: ?booga unit} ] 

------------------------------------------------------------



    partial def free_vars: Ty -> PHashSet Nat 
    | .bvar id => {} 
    | .fvar id => PersistentHashSet.empty.insert id 
    | .unit => {} 
    | .top => {} 
    | .bot => {} 
    | .tag l ty => (free_vars ty) 
    | .field l ty => (free_vars ty)
    | .union ty1 ty2 => (free_vars ty1).fold insert (free_vars ty2)
    | .inter ty1 ty2 => (free_vars ty1).fold insert (free_vars ty2)
    | .case ty1 ty2 => (free_vars ty1).fold insert (free_vars ty2)
    | .exis n ty_c1 ty_c2 ty =>
      -- (free_vars ty_c1);(free_vars ty_c2);(free_vars ty)
      (free_vars ty)
    | .univ n ty_c1 ty_c2 ty =>
      -- (free_vars ty_c1);(free_vars ty_c2);(free_vars ty)
      (free_vars ty)
    | .recur ty => (free_vars ty)

    partial def free_vars_env (env_ty : PHashMap Nat Ty) (ty : Ty) : PHashSet Nat :=  
      free_vars (reduce env_ty ty)



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



    def nested_pairs : (List Ty) -> Ty 
    | [] => .unit 
    | ty :: tys => [lesstype| ⟨ty⟩ * ⟨nested_pairs tys⟩ ]

    def no_function_types: Ty -> Bool
    | .bvar _ => true  
    | .fvar _ => true  
    | .unit => true 
    | .top => true 
    | .bot => true 
    | .tag _ content => no_function_types content
    | .field _ content => no_function_types content
    | .union ty1 ty2 => 
      no_function_types ty1 && 
      no_function_types ty2
    | .inter ty1 ty2 => 
      no_function_types ty1 && 
      no_function_types ty2
    | .case _ _ => false
    | .exis n ty_c1 ty_c2 ty_pl =>
      no_function_types ty_c1 && 
      no_function_types ty_c2 && 
      no_function_types ty_pl
    | .univ n ty_c1 ty_c2 ty_pl =>
      no_function_types ty_c1 && 
      no_function_types ty_c2 && 
      no_function_types ty_pl
    | .recur content => no_function_types content 

    partial def map_keys_to_constraints (context : Context) : PHashMap Nat (PHashSet (Ty × Ty)) :=
      let constraints := (
          context.env_simple.toList.map (fun (k,rhs) => (Ty.fvar k, rhs)) ++
          context.env_relational.toList
      )
      constraints.foldl (fun acc constraint => 
        let (lhs, _) := constraint
        let fids := toList (free_vars lhs)
        fids.foldl (fun acc fid =>
          match acc.find? fid with
          | some constraints => acc.insert fid (constraints.insert constraint)
          | none => acc.insert fid (empty.insert constraint)
        ) acc
      ) {}


    partial def reachable_constraints (map_kcs : PHashMap Nat (PHashSet (Ty × Ty))) (ty : Ty) : List (Ty × Ty) :=
      let fvs := PHashSet.toList (free_vars ty)
      List.bind fvs (fun key =>
        match map_kcs.find? (key) with
        | some constraints => 
          let cs := toList constraints
          cs ++ (cs.bind (fun (_, rhs) =>
            reachable_constraints map_kcs rhs
          ))
        | none => []
      )


    def generalize (boundary : Nat) (context : Context) (ty : Ty) : Ty := 
      --------------------------------------
      -- boundary prevents overgeneralizing

      -- sub in simple types; 
      -- subbing prevents strengthening from the outside in 
      -- only the body type (conclusion) can safely strengthen the parameter type (the premise)  
      -- subbing does not prevent weakening, as weakining is handles adding unions of fresh variables  
      --------------------------------------

      let ty := simplify (subst context.env_simple ty)

      let map_kcs := map_keys_to_constraints context
      let constraints := reachable_constraints map_kcs ty

      let fvs_constraints := constraints.foldl (fun acc (lhs, rhs) =>
        (free_vars lhs) + (free_vars rhs) + acc
      ) {} 
      
      let fids := List.filter (fun id => id >= boundary) (
        toList ((free_vars ty) + fvs_constraints)
      )

      if fids.isEmpty then
          ty
      else if no_function_types ty then
        let env_sub := PHashMap.from_list (
          fids.map (fun fid => (fid, Ty.bot))
        )
        simplify (subst env_sub ty)
      else if constraints.isEmpty then
        [lesstype|
          forall [⟨fids.length⟩] ⟨abstract fids 0 ty⟩
        ]
      else
        intersect_over (fun (ty_lhs, ty_rhs) => 
          let ty_ex := [lesstype|
            {[⟨fids.length⟩] ⟨abstract fids 0 ty⟩ with ⟨abstract fids 0 ty_lhs⟩ <: ⟨abstract fids 0 ty_rhs⟩}
            
          ]
          [lesstype| forall [1] β[0] <: ⟨ty_ex⟩ have β[0]]
        ) constraints

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
        Ty.recur (instantiate 0 [(Ty.fvar key)] ty)
        -- subst (PHashMap.from_list [(key, [lesstype| β[0] ])]) [lesstype| (induct ⟨ty⟩) ] 
      else
        ty 

    partial def occurs_not (key : Nat) (m : PHashMap Nat Ty) (ty : Ty) : Ty :=
      if (free_vars_env m ty).contains key then
        .bot
      else
        ty


    partial def subst_default (sign : Bool) : Ty -> Ty
    | .bvar id => .bvar id  
    | .fvar id => if sign then .bot else [lesstype| ⊤ ] 
    | .unit => .unit 
    | .top => .top
    | .bot => .bot 
    | .tag l ty => .tag l (subst_default sign ty) 
    | .field l ty => .field l (subst_default sign ty) 
    | .union ty1 ty2 =>
      .union (subst_default sign ty1) (subst_default sign ty2)
    | .inter ty1 ty2 =>
      .inter (subst_default sign ty1) (subst_default sign ty2)
    | .case ty1 ty2 => .case (subst_default (!sign) ty1) (subst_default sign ty2)
    | .exis n cty1 cty2 ty => 
      -- can't sub away if constrained
      .exis n cty1 cty2 ty
    | .univ n cty1 cty2 ty => 
      -- can't sub away if constrained
      .univ n cty1 cty2 ty
    | .recur ty => .recur (subst_default sign ty)


    partial def equal (env_ty : PHashMap Nat Ty) (ty1 : Ty) (ty2 : Ty) : Bool :=
      let ty1 := simplify (subst env_ty ty1)
      let ty2 := simplify (subst env_ty ty2)
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

    partial def extract_record_labels : Ty -> PHashSet String
    | .field l ty => 
      empty.insert l
    | .union ty1 ty2 => 
      (extract_record_labels ty1) + (extract_record_labels ty2)
    | .inter ty1 ty2 => 
      match linearize_fields (Ty.inter ty1 ty2) with
      | .none => {} 
      | .some fields => from_list (fields.map (fun (l, _) => l))
    | .exis n ty_c1 ty_c2 ty => (extract_record_labels ty)
    | .recur ty => extract_record_labels ty
    | _ => {} 

    partial def extract_label_list (ty : Ty) : List String :=
      toList (extract_record_labels ty)

    partial def wellfounded (n : Nat) : Ty -> Bool
    | .bvar id => (List.range n).all (fun tar => id != tar)
    | .fvar _ => true 
    | .unit => true 
    | .top => true 
    | .bot => true 
    | .tag _ _ => true 
    | .field _ ty => wellfounded n ty
    | .union ty1 ty2 =>
      wellfounded n ty1 && wellfounded n ty2
    | .inter ty1 ty2 =>
      match (extract_nested_fields (.inter ty1 ty2)) with
      | [] => false
      | fields => fields.any (fun ty' => wellfounded n ty')
    | .case _ _ => false
    | .exis n' ty_c1 ty_c2 ty' => 
      wellfounded (n + n') ty'
    | .univ _ _ _ _ => false 
    | .recur _ => false 

    def matchable (fields : List Ty) : Bool := 
      List.any fields (fun ty_fd =>
        match ty_fd with
        | Ty.tag _ _ => true 
        | _ => false
      )  


    partial def unify (i : Nat) (context : Context)
    : Ty -> Ty -> (Nat × List Context)

    -- existential quantifier elimination (closed variables) 
    | .exis n ty_c1 ty_c2 ty1, ty2 => (
      let bound_start := i
      let (i, ids) := (i + n, (List.range n).map (fun j => i + j))
      let bound_end := i
      let is_bound_var := (fun i' => bound_start <= i' && i' < bound_end)

      let args := ids.map (fun id => Ty.fvar id)
      let ty_c1 := instantiate 0 args ty_c1
      let ty_c2 := instantiate 0 args ty_c2
      let ty1 := instantiate 0 args ty1

      let (i, contexts) := (unify i context ty_c1 ty_c2)
      -- vacuous truth unsafe: given P |- Q, if P is incorreclty false, then P |- Q is incorrecly true (which is unsound)
      if contexts.isEmpty then (
        let is_recur_type := match ty_c2 with 
        | Ty.recur _ => true
        | _ => false

        let rlabels := extract_record_labels ty_c1 
        let is_consistent_variable_record := !rlabels.isEmpty && List.all (toList (extract_record_labels ty_c2)) (fun l =>
            rlabels.contains l 
          )
        let ty_key := (simplify (subst context.env_simple ty_c1))
        let unmatchable := !(matchable (extract_nested_fields ty_key))

        if is_recur_type && unmatchable && is_consistent_variable_record then

          -- invariant: variables in env_relational cannot be assigned in env_simple
          let context := {context with env_relational := context.env_relational.insert ty_key ty_c2}
          let (i, contexts) := (unify i context ty1 ty2) 

          let result_safe := contexts.all (fun context => context.env_simple.toList.all (fun (key, _) =>
            not (is_bound_var key)
          ))
          if result_safe then 
            (i, contexts)
            -- TODO: is it safe to allow closed variables? 
            -- should be since it has been confirmed by subtyping by this point
            -- existential may be converted to universal via generalization. 
            -- TODO: generalization should first existentially quantify to avoid over generalizing. 
            -- (i, contexts.map (fun context =>
            --   {context with env_relational := context.env_relational.erase ty_key}
            -- ))
          else
            (i, [])


        else 
          (i, []) 
      ) else ( 
        ------------------------------------------------------------
        -- collapsing: necessarying for soundness 
        ------------------------------------------------------------
        let ty1_unioned := List.foldr (fun context ty_acc => 
          (.union (generalize bound_start context ty1) ty_acc)
        ) Ty.bot contexts 

        (unify i context ty1_unioned ty2) 
      )
    ) 

    -- universal quantifier introduction (closed variables)
    | ty1, .univ n ty_c1 ty_c2 ty2  => (
      let bound_start := i
      let (i, ids) := (i + n, (List.range n).map (fun j => i + j))
      let bound_end := i
      let is_bound_var := (fun i' => bound_start <= i' && i' < bound_end)

      let args := ids.map (fun id => Ty.fvar id)
      let ty_c1 := instantiate 0 args ty_c1
      let ty_c2 := instantiate 0 args ty_c2
      let ty2 := instantiate 0 args ty2

      let (i, contexts) := (unify i context ty_c1 ty_c2)

      -- vacuous truth unsafe: given P |- Q, if P is incorreclty false, then P |- Q is incorrecly true (which is unsound)
      if contexts.isEmpty then
        (i, [])
      else (
        let ty2_inter := List.foldr (fun context ty_acc => 
          ---------
          -- broken: generalization causes non-termination; need to understand this 
          ---------
          -- (.inter (generalize bound_start context ty2) ty_acc)
          ----------------------------------
          (simplify (subst context.env_simple (.inter ty2 ty_acc)))
        ) Ty.top contexts 

        (unify i context ty1 ty2_inter)
      )
    )

    -- existential quantifier introduction (open variables) 
    | ty', .exis n ty_c1 ty_c2 ty =>
      let (i, args) := (
        i + n, 
        (List.range n).map (fun j => Ty.fvar (i + j))
      )

      let ty_c1 := instantiate 0 args ty_c1
      let ty_c2 := instantiate 0 args ty_c2
      let ty := instantiate 0 args ty

      -- NOTE: unify constraint last, as quantified variables should react to unification of payloads
      bind_nl (unify i context ty' ty) (fun i context => 
        unify i context ty_c1 ty_c2
      )


    -- universal quantifier elimination (open variables)
    | .univ n ty_c1 ty_c2 ty1, ty2 =>
      let bound_start := i
      let (i, args, set_expandable) := (
        i + n, 
        (List.range n).map (fun j => Ty.fvar (i + j)),
        if ty_c1 == Ty.unit && ty_c2 == Ty.unit then
          -- widening/exapnding is caused from the outside in 
          context.set_expandable + (from_list ((List.range n).map (fun j => (i + j))))
        else
          context.set_expandable
      )
      let context := {context with set_expandable := set_expandable}



      let bound_indicies := (List.range n).map (fun j => bound_start + j)

      let ty_c1 := instantiate 0 args ty_c1
      let ty_c2 := instantiate 0 args ty_c2
      let ty1 := instantiate 0 args ty1

      -- NOTE: unify constraint last, as quantified variables should react to unification of payloads
      bind_nl (unify i context ty1 ty2) (fun i context => 
        -- ensure failure instead of narrowing 
        -- this unification is from the outside in
        -- whereas, narrowing should only be used from the inside out
        let env_sub := PHashMap.from_list (
          bound_indicies.bind (fun bid => 
          match context.env_simple.find? bid with
          | some ty_b => [(bid, ty_b)]
          | none => []
          )
        ) 
        let ty_c1 := (simplify (subst env_sub ty_c1))
        let ty_c2 := (simplify (subst env_sub ty_c2))

        let (i,contexts) := (unify i context ty_c1 ty_c2)
        if contexts.isEmpty then
          -------------------------------
          -- TODO: delete saveing the relation subtyping
          -- seems odd to state an assumption should hold by return it in the context
          -------------------------------
          -- let is_recur_type := match ty_c2 with 
          -- | Ty.recur _ => true
          -- | _ => false

          -- let rlabels := extract_record_labels ty_c1 
          -- let is_consistent_variable_record := !rlabels.isEmpty && List.all (toList (extract_record_labels ty_c2)) (fun l =>
          --     rlabels.contains l 
          --   )
          -- let ty_key := (simplify (subst context.env_simple ty_c1))
          -- let unmatchable := !(matchable (extract_nested_fields ty_key))

          -- if is_recur_type && unmatchable && is_consistent_variable_record then
          --   (i, [context])
          -- else 
          --   (i, []) 
          -------------------------------
          (i, [])
        else
          (i, contexts)
      )

    ---------------------------------------------------------------
    -- free variables
    ---------------------------------------------------------------
    | (.fvar id1), (.fvar id2) => 
      match (context.env_simple.find? id1, context.env_simple.find? id2) with 
      | (.none, .none) => 
        if id1 == id2 then
          (i, [context])
        else
          -- NOTE: save as rhs maps to lhs. Enables freed existential vars (rhs) to map to closed existential vars (lhs). 
          (i, [{context with env_simple := context.env_simple.insert id2 (Ty.fvar id1)}])
      | (_, .some ty) => unify i context (.fvar id1) ty 
      | (.some ty', _) => unify i context ty' (.fvar id2) 

    | .fvar id, ty  => 
      ----------------------------
      -- adjustment updates the variable assignment to lower the upper bound 
      ---------------------------
      match context.env_simple.find? id with 
      | none => 
        (i, [{context with env_simple := context.env_simple.insert id (occurs_not id context.env_simple ty)}])
      | some ty' => 
        let (i, contexts) := (unify i context ty' ty)
        if contexts.isEmpty then
          (i, [{context with env_simple := context.env_simple.insert id (occurs_not id context.env_simple (Ty.inter ty ty'))}])
        else
          (i, contexts)
      ---------------------------------------

    | ty', .fvar id => 
      ----------------------
      -- adjustment here records observed types; based on unioning fresh variable
      -- assymetrical mechanism, since free variables have the meaning of Top, and environment tracks upper bounds
      -- when the environment is packed as a constraint; it becomes id <: ty', so we need union to make id <: ty' | Top
      --------------------
      match context.env_simple.find? id with 
      | none => 
        let expandable := context.set_expandable.find? id != .none
        let (i, ty_assign) := (
          if expandable then
            (i + 1, Ty.union (Ty.fvar i) ty') 
          else
            (i, ty')
        )
        (i, [{context with env_simple := context.env_simple.insert id (roll_recur id context.env_simple ty_assign)}])
      | some ty => 
        (unify i context ty' ty) 
      ---------------------------------------

    | .case ty1 ty2, .case ty3 ty4 =>

      bind_nl (unify i context ty3 ty1) (fun i context =>
        (unify i context ty2 ty4)
      ) 

    | .bvar id1, .bvar id2  =>
      if id1 = id2 then 
        (i, [context])
      else
        (i, [])

    | .bot, _ => (i, [context])
    | _, .top => (i, [context])
    | .unit, .unit => (i, [context])

    | .tag l' ty', .tag l ty =>
      if l' = l then
        unify i context ty' ty
      else
        (i, [])

    | .field l' ty', .field l ty =>
      if l' == l then
        unify i context ty' ty
      else
        (i, [])

    | .recur ty1, ty2 =>
      if equal context.env_simple (.recur ty1) ty2 then
        (i, [context])
      else
        -- using induction hypothesis, ty1 ≤ ty2; safely unroll
        let ty1 := instantiate 0 [ty2] ty1
        unify i context ty1 ty2

    | ty', .recur ty =>
      let ty' := (simplify (subst context.env_simple ty'))
      match (extract_nested_fields ty') with
      | [] => 
        if wellfounded 1 ty then
          unify i context ty' (instantiate 0 [Ty.recur ty] ty) 

        else
          (i, []) 
      | fields =>
        if matchable fields then 
          if wellfounded 1 ty then
            unify i context ty' (instantiate 0 [Ty.recur ty] ty)
          else
            (i, []) 
        else
          let ty_key := simplify (subst context.env_simple ty')
          match context.env_relational.find? ty_key with
          | .some ty_cache => 
            let context := {context with env_relational := context.env_relational.insert ty' ty_cache}
            unify i context ty_cache (Ty.recur ty)
          | .none =>  
            -- NOTE: cannot save in relational type
            -- the variables may have already be assigned in env_simple
            -- must respect invariant that env_simple and env_relational have disjoint key variables
            (i, []) 

    | Ty.union ty1 ty2, ty => 
      bind_nl (unify i context ty1 ty) (fun i context =>
        (unify i context ty2 ty)
      )

    | ty, .union ty1 ty2 => 
      let (i, contexts_ty1) := (unify i context ty ty1)
      let (i, contexts_ty2) := (unify i context ty ty2)
      (i, contexts_ty1 ++ contexts_ty2)


    | ty, .inter ty1 ty2 => 
      bind_nl (unify i context ty ty1) (fun i context =>
        (unify i context ty ty2)
      )

    | .inter ty1 ty2, ty => 
      let (i, contexts_ty1) := (unify i context ty1 ty)
      let (i, contexts_ty2) := (unify i context ty2 ty)
      (i, contexts_ty1 ++ contexts_ty2)

    | _, _ => (i, []) 

    partial def union_all : (List Ty) -> Option Ty
      | [] => none
      | t::ts =>
        let ts := List.filter
          (fun t' => not (t == t'))
          ts
        match union_all ts with
          | .none => .some t
          | .some t' => Ty.union t t'


    partial def unify_reduce_env (i : Nat) (env_simple : PHashMap Nat Ty) (ty1) (ty2) (ty_result) :=
      let context : Context := Context.mk env_simple empty empty
      let (_, contexts) : Nat × List Context := (unify i context ty1 ty2)
      List.foldr (fun context ty_acc => 
        let env_simple := Context.env_simple context
        simplify (subst env_simple (Ty.union ty_result ty_acc))
      ) Ty.bot contexts 

      
    partial def unify_reduce (i : Nat) (ty1) (ty2) (ty_result) :=
      let context : Context := ⟨empty, empty, empty⟩
      let (_, contexts) := (unify i context ty1 ty2)
      generalize i context (
        List.foldr (fun context ty_acc => 
          let env_simple := Context.env_simple context
          simplify (subst env_simple (Ty.union ty_result ty_acc))
        ) Ty.bot contexts
      )

    partial def unify_reduce_expand (i : Nat) (exp : List Nat) (ty1) (ty2) (ty_result) :=
      let context : Context := ⟨empty, empty, from_list exp⟩
      let (_, contexts) := (unify i context ty1 ty2)
      generalize i context (
        List.foldr (fun context ty_acc => 
          let env_simple := Context.env_simple context
          simplify (subst env_simple (Ty.union ty_result ty_acc))
        ) Ty.bot contexts
      )


    partial def unify_simple (i : Nat) (ty1) (ty2) :=
      let context : Context := ⟨empty, empty, empty⟩
      (unify i context ty1 ty2)

    partial def unify_decide (i : Nat) (ty1) (ty2) :=
      let context : Context := ⟨empty, empty, empty⟩
      let (_, result) := (unify i context ty1 ty2)
      !result.isEmpty

    def combine (icontexts : (Nat × List Context)) (ty : Ty) :=
      let (i, contexts) := icontexts
      (i, contexts.map fun context => (context, ty))

    def to_pair_type : Ty -> Ty 
    | .case ty1 ty2 => 
      [lesstype| ⟨ty1⟩ * ⟨ty2⟩ ] 
    | [lesstype| ⊤ ] =>  [lesstype| ⊥ ]
    | _ =>  [lesstype| ⊤ ]

    def get_prem : Ty -> Ty 
    | .case ty1 _ => ty1 
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



    -- structure Guide where
    --   env_tm : PHashMap Nat Ty
    --   ty_expected : Ty
    -- deriving Repr

    -- structure Contract where
    --   i : Nat
    --   env_ty : PHashMap Ty Ty 
    --   guides : List (Nat × Guide) -- [..., (hole variable, guide), ...]
    --   t : Tm
    --   ty : Ty 
    -- deriving Repr



    partial def infer (i : Nat) (context : Ty.Context) (env_tm : PHashMap Nat Ty) (t : Tm) (ty : Ty) : 
    (Nat × List (Ty.Context × Ty)) :=
    match t with
    | hole => 
      (i, [(context, Ty.top)])
    | .unit => 
      let (i, contexts) := (Ty.unify i context Ty.unit ty) 
      (i, contexts.map fun context => (context, Ty.unit))
    | bvar _ => (i, []) 
    | fvar id =>
      match (env_tm.find? id) with
      | some ty' => 
        Ty.combine (Ty.unify i context ty' ty) ty'
      | none => (i, [])

    | .tag l t1 =>   
      let (i, ty1) := (i + 1, Ty.fvar i)
      bind_nl (Ty.unify i context (Ty.tag l ty1) ty) (fun i context =>
      bind_nl (infer i context env_tm t1 ty1) (fun i (context, ty1') =>
        (i, [(context, Ty.tag l ty1')])
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
        bind_nl acc (fun i (context, ty_acc) =>
        bind_nl (infer i context env_tm t1 ty1) (fun i (context, ty1') =>
          (i, [(context, Ty.inter (Ty.field l ty1') ty_acc)])
        ))
      )

      let init := Ty.combine (Ty.unify i context ty' ty) [lesstype| ⊤ ]
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
        bind_nl acc (fun i (context, ty_acc) =>
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
          bind_nl (infer i context (env_tm ; env_pat) p ty_p) (fun i (context, ty_p') =>
          bind_nl (infer i context (env_tm ; env_pat) b ty_b) (fun i (context, ty_b') =>
              (i, [(context, Ty.simplify (Ty.inter (Ty.case ty_p' ty_b') ty_acc))])
          )))
        )

      let init := Ty.combine (Ty.unify i context ty' ty) [lesstype| ⊤ ]
      List.foldr f_step init fs_typed

    | .proj t1 l =>
      bind_nl (infer i context env_tm t1 (Ty.field l ty)) (fun i (context, ty1') =>
      let (i, ty') := (i + 1, Ty.fvar i)
      bind_nl (Ty.unify i context ty1' (Ty.field l ty')) (fun i context =>
        (i, [(context, ty')])
      ))

    | .app t1 t2 =>
    ------------------------------ 
    ------------------------------ 
      let (i, ty2) := (i + 1, Ty.fvar i)
      bind_nl (infer i context env_tm t2 ty2) (fun i (context, ty2') =>
      bind_nl (infer i context env_tm t1 (Ty.case ty2' ty)) (fun i (context, ty1) =>
      let (i, ty') := (i + 1, Ty.fvar i)
      bind_nl (Ty.unify i context ty1 (Ty.case ty2' ty')) (fun i context =>
        (i, [(context, ty')])
      )))
      ------------------------------------------
      ---- alternative 
      -------------------------------------------------------
      -- let (i, ty2) := (i + 1, Ty.fvar i)
      -- let (i, ty') := (i + 1, Ty.fvar i)
      -- bind_nl (infer i context env_tm t1 (Ty.case ty2 ty)) (fun i (context, ty1) =>
      -- bind_nl (infer i context env_tm t2 ty2) (fun i (context, ty2') =>
      -- bind_nl (Ty.unify i context {} {} ty1 (Ty.case ty2' ty')) (fun i context =>
      --   (i, [(context, ty')])
      -- )))
      ----------------------------------------------

    | .letb op_ty1 t1 t => 

      let (i, ty1) := match op_ty1 with
      | some ty1 => (i, ty1)
      | none => (i + 1, Ty.fvar i)

      let free_var_boundary := i

      if t1 == Tm.hole then
        let (i, x, env_tmx) := (i + 1, fvar i, PHashMap.from_list [(i, ty1)]) 
        let t := instantiate 0 [x] t 
        (infer i context (env_tm ; env_tmx) t ty) 
      else
        --------------------------------------------------------------------------------
        -- collapsing
        --------------------------------------------------------------------------------
        let (i, contexts) := (infer i context env_tm t1 ty1) 
        let ty1_schema := List.foldr (fun (context, ty1') ty_acc => 
          let ty1_schema := Ty.generalize free_var_boundary context ty1'
          (Ty.union ty1_schema ty_acc)
        ) Ty.bot contexts 
        let (i, x, env_tmx) := (i + 1, fvar i, PHashMap.from_list [(i, ty1_schema)]) 
        let t := instantiate 0 [x] t 

        -- unification check, since downward propagation cannot check against a full union 
        bind_nl (Ty.unify i context ty1_schema ty1) (fun i context => 
          (infer i context (env_tm ; env_tmx) t ty) 
        )
        --------------------------------------------------------------------------------

        --------------------------------------------------------------------------------
        -- old version without collapsing 
        --------------------------------------------------------------------------------
        -- bind_nl (infer i context env_tm t1 ty1) (fun i (context, ty1') =>
        --   let ty1_schema := Ty.generalize free_var_boundary context ty1'
        --   -- let ty1_schema := ty1'

        --   let (i, x, env_tmx) := (i + 1, fvar i, PHashMap.from_list [(i, ty1_schema)]) 
        --   let t := instantiate 0 [x] t 

        --   (infer i context (env_tm ; env_tmx) t ty) 

        -- )
        --------------------------------------------------------------------------------


    | .fix t1 =>

      let (i, ty_prem) := (i + 1, Ty.fvar i) 
      let (i, ty_conc) := (i + 1, Ty.fvar i) 
      bind_nl (infer i context env_tm t1 (Ty.case ty_prem ty_conc)) (fun i (context, ty1') =>
        let ty_prem := (Ty.reduce context.env_simple ty_prem)
        let ty_conc := (Ty.reduce context.env_simple ty_conc)

        ------------------------------------------------------
        -- TODO: factor out this rewriting with higher order function 
        -- TODO: need to avoid relational types in parameter
        -------------------------------------------------------
        -- let ty_param_content := List.foldr (fun ty_case ty_acc =>
        --   let fvs := (Ty.free_vars ty_case).toList.bind (fun (k , _) => [k])
        --   let fvs_prem :=  (Ty.free_vars ty_prem)
        --   let ty_choice := (
        --     if List.any fvs (fun id => fvs_prem.find? id != none) then
        --       let fixed_point := fvs.length
        --       [lesstype|
        --         {[⟨fvs.length⟩] ⟨Ty.abstract fvs 0 (Ty.get_prem ty_case)⟩ with 
        --           ⟨Ty.abstract fvs 0 (Ty.get_prem ty_prem)⟩ <: β[⟨fixed_point⟩] 
        --         } 
        --       ]
        --     else if fvs.length > 0 then
        --       [lesstype| {[⟨fvs.length⟩] ⟨Ty.abstract fvs 0 (Ty.get_prem ty_case)⟩} ]
        --     else
        --       (Ty.get_prem ty_case)
        --   )

        --   (Ty.union ty_choice ty_acc) 
        -- ) [lesstype| ⊥ ] (Ty.split_intersectionss ty_conc)

        -- let ty_param := [lesstype| induct ⟨ty_param_content⟩ ]
        ------------------------------------------------------
        let (i, ty_param) := (i + 1, Ty.fvar i)
        ------------------------------------------------------

        let ty_content := List.foldr (fun ty_case ty_acc =>
          let fvs := toList (Ty.free_vars ty_case)
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

        -- NOTE: constraint that ty' <= ty_prem is built into inductive type
        let relational_type := [lesstype| induct ⟨ty_content⟩ ]
        let ty' := [lesstype| forall [1] β[0] <: ⟨ty_param⟩ have β[0] -> {[1] β[0] with β[1] * β[0] <: ⟨relational_type⟩} ] 
        -- TODO: convert to version without existential
        -- let ty' := [lesstype| forall [1] β[0] * β[1] <: ⟨relational_type⟩ have β[0] -> β[1] ] 
        bind_nl (Ty.unify i context ty' ty) (fun i context =>
          (i, [(context, ty')])
        )
      )
      --------------
      -- bind_nl (Ty.unify i context ty1' (.case ty_prem ty)) (fun i context =>
      -- )
      --------------


    partial def infer_simple i (t : Tm) :=
      let context : Ty.Context := ⟨empty, empty, empty⟩
      (infer (i + 1) context {} t (Ty.fvar i))

    partial def infer_reduce_wt (i : Nat) (t : Tm) (ty : Ty): Ty :=
      let boundary := i 
      let context : Ty.Context := ⟨empty, empty, empty⟩
      let (_, contexts) := (infer i context {} t ty)
      List.foldr (fun (context, ty') ty_acc => 
        let ty' := Ty.simplify ((Ty.subst context.env_simple (Ty.union ty' ty_acc)))
        Ty.generalize boundary context ty'
      ) Ty.bot contexts


    partial def infer_reduce (i : Nat) (t : Tm) : Ty := infer_reduce_wt (i + 1) t (Ty.fvar i)

    -- structure Work where
    --   cost : Nat
    --   i : Nat
    --   guides : PHashMap Nat Guide
    --   patches : PHashMap Nat Tm 
    --   t : Tm
    -- deriving Repr



    -- def Work.le (x y: Work): Bool := x.cost <= y.cost

    -- def Work.Queue := BinomialHeap Work Work.le

    -- partial def cost : Tm -> Nat
    -- | hole => 1 
    -- | .unit => 1 
    -- | bvar id => 1 
    -- | fvar id => 1
    -- | tag l t => 1 + (cost t)
    -- | record entries => 
    --   List.foldl (fun cost' (l, t) => cost' + (cost t)) 1 entries
    -- | func cases =>
    --   List.foldl (fun cost' (p, t_b) => cost' + (cost t_b)) 1 cases
    -- | proj t l => 1 + (cost t)
    -- | app t1 t2 => 1 + (cost t1) + (cost t2)
    -- | letb ty t1 t2 => 1 + (cost t1) + (cost t2)
    -- | .fix t => 1 + (cost t)

    -- partial def subst (m : PHashMap Nat Tm) : Tm -> Tm 
    -- | hole => hole 
    -- | .unit => .unit 
    -- | bvar id => bvar id 
    -- | fvar id => (match m.find? id with
    --   | some t => subst m t 
    --   | none => .fvar id
    -- )
    -- | tag l t => tag l (subst m t)
    -- | record entries => 
    --   let entries' := List.map (fun (l, t) => (l, subst m t)) entries 
    --   record entries'
    -- | func cases =>
    --   let cases' := List.map (fun (p, t_b) => 
    --     (p, subst m t_b)
    --   ) cases 
    --   func cases'
    -- | proj t l => proj (subst m t) l
    -- | app t1 t2 => app (subst m t1) (subst m t2)
    -- | letb ty t1 t2 => letb ty (subst m t1) (subst m t2)
    -- | .fix t => .fix (subst m t)

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
  -- expected: ?nil unit
  #eval unify_reduce 30
  [lesstype| {β[0] with ?succ ?zero unit * β[0] <: ⟨nat_list⟩} ]
  [lesstype| ?cons α[0] ] 
  [lesstype| α[0] ]


  -- expected: ?cons ?nil unit
  #eval unify_reduce 30
  [lesstype| forall β[0] <: ⊤ have β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} ]
  [lesstype| ?succ ?succ ?zero unit -> ?cons α[0] ] 
  [lesstype| α[0] ]

  -- expected: ?cons ?nil unit
  #eval unify_reduce 30
  [lesstype| forall β[1] * β[0] <: ⟨nat_list⟩ have β[1] -> β[0]]
  [lesstype| ?succ ?succ ?zero unit -> ?cons α[0] ] 
  [lesstype| α[0] ]

  -- expected: true 
  #eval unify_decide 30
  [lesstype| forall β[0] <: α[11] have β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} ]
  [lesstype| forall β[1] * β[0] <: ⟨nat_list⟩ have β[1] -> β[0]]

  -- sound, but incomplete
  #eval unify_decide 30
  [lesstype| forall β[1] * β[0] <: ⟨nat_list⟩ have β[1] -> β[0]]
  [lesstype| forall β[0] <: ⟨nat_⟩ have β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} ]

  -- expected: false
  #eval unify_decide 20
  [lesstype| forall β[1] * β[0] <: ⟨nat_list⟩ have β[1] -> β[0]]
  [lesstype| ?succ ?succ ?zero unit -> ?cons ?nil unit ] 


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

  -- expected: true
  #eval unify_decide 0 even_list nat_list 

  -- expected: false 
  #eval unify_decide 0 nat_list even_list

  def even := [lesstype| 
    induct ?zero unit | ?succ ?succ β[0]
  ]

  ------------------------

  -- expected: true
  #eval unify_decide 0
  [lesstype| forall [1] β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} ]
  [lesstype| forall [1] β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} ]


  -- sound but incomplete; relational types shouldn't be used in universal 
  -- universal should only have simple constraints
  -- TODO: could restrict universal syntax to merge variable binding and constraint
  -- and also reduce universal to a single variable
  -- e.g. from forall [X] X <: T have X -> Y
  -- e.g. to forall [X <: T] X -> Y
  #eval unify_decide 0
  [lesstype| forall [1] β[0] * β[1] <: ⟨nat_list⟩ have β[0] -> β[1] ]
  [lesstype| forall [1] β[0] * β[1] <: ⟨nat_list⟩ have β[0] -> β[1] ]


  -- expected: ?cons ?nil unit
  #eval unify_reduce 10
  [lesstype| forall β[0] <: {[2] β[0] -> β[1] with β[0] * β[1] <: ⟨nat_list⟩} have β[0]]
  [lesstype| ?succ ?zero unit -> α[2]]
  [lesstype| α[2]]

  -- expected: ⊥
  #eval unify_reduce 10
  [lesstype| ?succ ?zero unit -> α[2]]
  [lesstype| forall β[0] <: {[2] β[0] -> β[1] with β[0] * β[1] <: ⟨nat_list⟩} have β[0]]
  [lesstype| α[2]]
  ----------------

  -- expected: ⊥
  #eval unify_reduce 10
  [lesstype| {[2] β[0] -> β[1] with β[0] * β[1] <: ⟨nat_list⟩}]
  [lesstype| ?succ ?zero unit -> α[2]]
  [lesstype| α[2]]

  -- expected: ?cons ?nil unit 
  #eval unify_reduce 10
  [lesstype| ?succ ?zero unit -> α[2]]
  [lesstype| {[2] β[0] -> β[1] with β[0] * β[1] <: ⟨nat_list⟩}]
  [lesstype| α[2]]


  -- expected: true
  #eval unify_decide 10 
  [lesstype| forall [1] β[0] <: α[0] have β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} ]
  [lesstype| forall [1] β[0] <: α[0] have β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} ]

  -- expected: true
  #eval unify_decide 10 
  [lesstype| α[1] -> {β[0] with α[1] * β[0] <: ⟨nat_list⟩} ]
  [lesstype| α[2] -> {β[0] with α[2] * β[0] <: ⟨nat_list⟩} ]

  #eval unify_simple 10 
  [lesstype| α[1] -> α[3] ]
  [lesstype| α[2] -> α[4] ]

  -- expected: true 
  #eval unify_decide 10 
  [lesstype| {β[0] with α[1] * β[0] <: ⟨nat_list⟩} ]
  [lesstype| {β[0] with α[1] * β[0] <: ⟨nat_list⟩} ]

  -- expected: false 
  #eval unify_decide 10 
  [lesstype| {β[0] with α[1] * β[0] <: ⟨nat_list⟩} ]
  [lesstype| {β[0] with α[2] * β[0] <: ⟨nat_list⟩} ]

  -- expected: true
  #eval unify_decide 10 
  [lesstype| {α[1] * β[0] with α[1] * β[0] <: ⟨nat_list⟩} ]
  [lesstype| {α[2] * β[0] with α[2] * β[0] <: ⟨nat_list⟩} ]

  -- expected: true
  #eval unify_decide 10 
  [lesstype| {β[0] * β[1] with β[0] * β[1] <: ⟨nat_list⟩} ]
  [lesstype| {β[0] * β[1] with β[0] * β[1] <: ⟨nat_list⟩} ]

  -- expected: true
  #eval unify_decide 10 
  [lesstype| {β[0] with β[0] <: ⟨nat_list⟩} ]
  [lesstype| {β[0] with β[0] <: ⟨nat_list⟩} ]

  -- expected: true
  #eval unify_decide 10 
  [lesstype| ⟨nat_list⟩ ]
  [lesstype| ⟨nat_list⟩ ]
---------------


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


  -- path discrimination

  -- expected: ?cons ?nil unit
  #eval infer_reduce 0 [lessterm|
    let y[0] : (?zero unit -> ?nil unit) & (?succ ?zero unit -> ?cons ?nil unit) = _ in 
    (y[0] (#succ #zero ()))
  ]

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

  -- expected: ?cons ?nil unit
  #eval infer_reduce 0 [lessterm|
    let y[0] : forall β[0] <: ⟨nat_⟩ have β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} = _ in 
    (y[0] (#succ #zero ()))
  ]

  -- expected: ⊥  
  -- expansion causes type-checking constraint to fail; since param type is allowed to be anything 
  #eval infer_reduce 0 [lessterm|
    let y[0] : forall β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} = _ in 
    (y[0] (#succ #zero ()))
  ]

---------------------------------------------------------------
  --------- recursive function (fix) type inference -----------

  #eval infer_reduce 0 [lessterm|
    fix(\ y[0] => (
    \ #zero () => #nil ()
    \ #succ y[0] => #cons (y[1] y[0])
    ))
  ]

  #eval infer_reduce 0 [lessterm|
    let y[0] = fix(\ y[0] => 
      \ #zero () => #nil ()
      \ #succ y[0] => #cons (y[1] y[0])
    ) in 
    y[0]
  ]

  -- expected: ?cons ?nil unit
  #eval infer_reduce 10 [lessterm|
    (fix(\ y[0] => ( 
      \ #zero () => #nil ()
      \ #succ y[0] => #cons (y[1] y[0])
    )) 
    (#succ #zero ())
    )
  ]

  -- expected: ?cons ?nil unit
  #eval infer_reduce 10 [lessterm|
    let y[0] = fix(\ y[0] => ( 
      \ #zero () => #nil ()
      \ #succ y[0] => #cons (y[1] y[0])
    )) in 
    (y[0] (#succ #zero ()))
  ]


  #eval unify_reduce 10 
  [lesstype|
  (forall [1]  β[0] <: α[3] have (β[0] -> {[1] β[0] with (β[1] * β[0]) <: 
    (induct (
        (?zero unit * ?nil unit) | 
        {[2] (?succ β[1] * ?cons β[0]) with (β[1] * β[0]) <: β[2]}))
  }))
  ]
  [lesstype| ?succ ?zero unit -> α[0] ]
  [lesstype| α[0] ]

  -------------------------------

  #eval Nameless.Tm.infer_reduce 0 [lessterm| 
      (fix (\ y[0] => (
        \ (#zero(), y[0]) => #true()  
        \ (#succ y[0], #succ y[1]) => (y[2] (y[0], y[1])) 
        \ (#succ y[0], #zero()) => #false() 
      )))
  ] 

  -- expected: ⊥  
  #eval Nameless.Tm.infer_reduce 0 [lessterm| 
    let y[0] : ?succ ?zero unit = 
    (
      (\ (y[0], y[1]) => (
        (
          (\ #true() => y[1] \ #false() => y[0]))
          ((
            \ (#zero(), y[0]) => #true()  
            \ (#succ y[0], #succ y[1]) => #false()
            \ (#succ y[0], #zero()) => #false() 
          )
          (y[0], y[1])) 
        )
      )
      ((#succ #succ #zero()), #succ #zero())
    ) 
    in
    y[0] 
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
    let y[0] = (\ y[0] => \ y[0] => (y[1], y[0])) in 
    ((y[0] #hello ()) #world ())
  ]

  #eval infer_reduce 0 [lessterm|
    (((\ y[0] => \ y[0] => (y[1], y[0])) #hello ()) #world ())
  ]

  -- NOTE: this requires subbing in unions to maintain expansion after let-poly generalization
  #eval infer_reduce 0 [lessterm|
    let y[0] : forall β[0] -> (β[0] -> (β[0] * β[0])) = _ in 
    let y[0] = (y[0] #hello ()) in
    (y[0] #world())
  ]

  -- narrowing
  #eval infer_reduce 0 [lessterm|
  let y[0] : ?uno unit -> unit = _ in 
  let y[0] : ?dos unit -> unit = _ in 
  (\ y[0] =>
    (y[2] y[0]))
  ]

  #eval infer_reduce 0 [lessterm|
  let y[0] : ?uno unit -> unit = _ in 
  let y[0] : ?dos unit -> unit = _ in 
  ((\ y[0] => (y[2] y[0])) #uno())
  ]

  #eval infer_reduce 0 [lessterm|
  let y[0] : ?uno unit -> unit = _ in 
  (y[0] #uno())
  ]

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
  -- expected: false
  #eval unify_decide 0 
    [lesstype| ?hello unit ] 
    [lesstype| induct ?wrong unit | β[0] ] 

  -- potentially diverges - inductive type not well founded
  -- expected: false
  #eval unify_decide 0 
    [lesstype| ?hello unit ] 
    [lesstype| induct β[0] ] 

  def bad_nat_list := [lesstype| 
    induct 
      (?zero unit * ?nil unit) | 
      {(β[0] * β[1]) with β[0] * β[1] <: β[2]}
  ]

  -- expected: false
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

  -- Note: is this in effect, the same thing as PDR/IC3?
  -- That is, whatever is learned to strengthen the conclusion 
  -- is automatically applied to preceding iterations 
  -- due to the wrapping type in inductive binding 
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

  -- expected: ?succ ?zero unit 
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

  -- -- broken 
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


-----------------------------------------------
  ------------ transpose_relation ----------------

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

  -- #eval [lessterm| 
  --   let y[0] : ⟨nat_⟩ -> ⟨list_⟩ = fix(\ y[0] =>
  --     \ #zero() => #nil()  
  --     \ #succ y[0] => #cons (y[1] y[0]) 
  --   )
  --   in
  --   y[0]
  -- ] 

  -- #eval Nameless.Tm.infer_reduce 0 [lessterm| 
  --   fix(\ y[0] =>
  --     \ #zero() => #nil()  
  --     \ #succ y[0] => #cons (y[1] y[0]) 
  --   )
  -- ]



  -- expected: true 
  #eval Nameless.Ty.unify_decide 0
  [lesstype| ⟨nat_list⟩ ]
  [lesstype| ⟨nat_⟩ * ⟨list_⟩ ]

  -- expected: false
  #eval Nameless.Ty.unify_decide 0
  [lesstype| ⟨nat_⟩ * ⟨list_⟩ ]
  [lesstype| ⟨nat_list⟩ ]

  -- expected: true 
  #eval Nameless.Ty.unify_decide 0
  [lesstype| {β[0] with β[0] * α[0] <: ⟨nat_list⟩} ]
  [lesstype| ⟨nat_⟩ ]

  -- expected: true 
  #eval Nameless.Ty.unify_decide 0
  [lesstype| forall β[0] <: ⟨nat_⟩ have β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} ]
  [lesstype| ⟨nat_⟩ -> ⟨list_⟩ ]

  -- expected: false 
  #eval Nameless.Ty.unify_decide 0
  [lesstype| ⟨nat_⟩ -> ⟨list_⟩ ]
  [lesstype| forall β[0] <: ⟨nat_⟩ have β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} ]

  -- expected: true 
  #eval Nameless.Ty.unify_decide 10
  [lesstype| {β[0] with β[0] <: ⟨list_⟩} ]
  [lesstype| ⟨list_⟩ ]


  ------------------------------


  -- expected: true 
  #eval Nameless.Ty.unify_decide 0
  [lesstype| ⟨nat_⟩ ]
  [lesstype|
    induct
      ?zero unit |
      {[2] ?succ β[0] with β[0] <: β[2]}
  ]

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

  ------- soundness ---------

  -- expected: true 
  #eval Nameless.Ty.unify_decide 0
  [lesstype| {β[0] with β[0] <: ?ooga unit} ]
  [lesstype|  ?ooga unit | ?booga unit]

  -- expected: false
  #eval Nameless.Ty.unify_decide 0
  [lesstype| {β[0] with β[0] <: (?three unit)} ]
  [lesstype| ?one unit ]

  -- expected: false
  #eval Nameless.Ty.unify_decide 0
  [lesstype| (?one unit | ?three unit) ]
  [lesstype| ?one unit ]

  -- expected: false
  #eval Nameless.Ty.unify_decide 0
  [lesstype| {β[0] with β[0] <: (?one unit | ?three unit)} ]
  [lesstype| ?one unit ]

  -- expected: false 
  #eval Nameless.Ty.unify_decide 0
  [lesstype| (?one unit * ?two unit) | (?three unit * ?four unit) ]
  [lesstype| (?three unit * ?four unit)  ]

  -- expected: false 
  #eval Nameless.Ty.unify_decide 0
  [lesstype| {β[0] with β[0] <: (?one unit * ?two unit) | (?three unit * ?four unit)} ]
  [lesstype| ?one unit * ?two unit ]

  -- expected: false 
  #eval Nameless.Ty.unify_decide 0
  [lesstype| {[2] β[0]  with β[0] * β[1] <: (?one unit * ?two unit) | (?three unit * ?four unit)} ]
  [lesstype| ?one unit ]

  -- expected: false 
  #eval Nameless.Ty.unify_decide 10
  [lesstype| {β[0] with β[0] * α[0] <: (?one unit * ?two unit) | (?three unit * ?four unit)} ]
  [lesstype| ?one unit  ]

  -- expected: false 
  #eval Nameless.Ty.unify_decide 0
  [lesstype| {[2] β[0] with β[0] * β[1] <: (?one unit * ?two unit) | (?three unit * ?four unit)} ]
  [lesstype| ?one unit ]

  -- expected: true 
  #eval Nameless.Ty.unify_decide 0
  [lesstype| {[2] β[0] with β[0] * β[1] <: (?one unit * ?two unit) | (?three unit * ?four unit)} ]
  [lesstype| ?one unit | ?three unit ]

  -- expected: false 
  #eval Nameless.Ty.unify_decide 0
  [lesstype| (?one unit * ?two unit) | (?three unit * ?four unit) ]
  [lesstype| ?one unit  ]

  -- expected: true 
  #eval Nameless.Ty.unify_decide 10 
  [lesstype| {β[0] with β[0] * α[0] <: (?one unit * ?two unit) | (?three unit * ?four unit)} ]
  [lesstype| ?one unit | ?three unit  ]

  -- expected: false 
  #eval Nameless.Ty.unify_decide 10 
  [lesstype| {β[0] with β[0] * α[0] <: (?one unit * ?two unit) | (?three unit * ?four unit)} ]
  [lesstype| ?one unit  ]



--------------------- universal introduction subtyping ----------------

  -- expected: false 
  #eval Nameless.Ty.unify_decide 0
  [lesstype| ?one unit  ]
  [lesstype| forall (β[0] | α[0]) <: (?one unit | ?two unit) & (?three unit | ?four unit)
    have β[0]
  ]

  -- expected: false 
  #eval Nameless.Ty.unify_decide 0
  [lesstype| ?one unit  ]
  [lesstype| (?one unit | ?two unit) & (?three unit | ?four unit) ]

  -- expected: false 
  #eval Nameless.Ty.unify_decide 0
  [lesstype| ?one unit  ]
  [lesstype| forall (β[0] | α[0]) <: (?one unit | ?two unit) * (?three unit | ?four unit)
   have β[0]
   ]

  -- expected: false 
  #eval Nameless.Ty.unify_decide 0
  [lesstype| ?one unit  ]
  [lesstype| (?one unit | ?two unit) * (?three unit | ?four unit) ]


---------------------------------
  #eval Nameless.Tm.infer_reduce 1 [lessterm| 
    let y[0] : α[0] = _ in
    y[0] 
  ] 

  def ooga := [lesstype| 
    induct
      {?zero unit * β[0]} |
      {?succ β[0] * ?succ β[1] with β[0] * β[1] <: β[2]}
  ]

  #eval Nameless.Ty.unify_reduce 10
  [lesstype| α[2] * α[3] -> {β[0] with (α[2] * β[0]) * (α[3] * β[0]) <: ⟨ooga⟩ * ⟨ooga⟩} ]
  [lesstype| α[0] * α[1] -> α[1] ]
  [lesstype| ?hmm unit ]


--------------------------------------------------------

  -- expected: terminates
  #eval Nameless.Tm.infer_reduce 0 [lessterm| 
    let y[0] : (forall [2] β[0] * β[1] -> {[1] β[0] with (β[0] * β[1]) <: ⟨nat_⟩ * ⟨nat_⟩}) = 
    (\ (y[0], y[1]) => y[0]) in
    y[0]
  ] 

--------------------------------------

  def nat_pair := [lesstype|
    induct
      {(?zero unit * ⟨nat_⟩)} 
      | 
      {(?succ β[0] * ?succ β[1]) with (β[0] * β[1]) <: β[2] } 
      | 
      {(?succ ⟨nat_⟩ * ?zero unit)}
  ]

  -- better: notions of ?zero and ?true appear in inferred type? 
  -- broken: type of max is bloated
  -- TODO: formulate the expected type of max
  -- NOTE: affected by erasing closed relational subtyping
  #eval Nameless.Tm.infer_reduce 0 [lessterm| 
    let y[0] = fix (\ y[0] =>
      \ (#zero(), y[0]) => #true()  
      \ (#succ y[0], #succ y[1]) => (y[2] (y[0], y[1])) 
      \ (#succ y[0], #zero()) => #false() 
    ) in
    let y[0] = (\ (y[0], y[1]) => 
      (
        (
        \ #true() => y[1]
        \ #false() => y[0]
        )
        (y[2] (y[0], y[1]))
      )
    ) in
    y[0]
    -- (y[0] (#succ #zero(), #succ #succ #succ #zero()))
    -- (y[0] (#succ #zero(), #zero()))
  ] 

/-
--
-/

------ debugging
  -- broken

  #eval Nameless.Tm.infer_reduce 0 [lessterm| 
    let y[0] = fix (\ y[0] =>
      \ (#zero(), y[0]) => #true()  
      \ (#succ y[0], #succ y[1]) => (y[2] (y[0], y[1])) 
      \ (#succ y[0], #zero()) => #false() 
    ) in
    let y[0] = (\ (y[0], y[1]) => 
        (y[2] (y[0], y[1]))
    ) in
    y[0]
  ] 
  -------------------

  -- broken
  -- expected: max of the two numbers
  -- non-termination
  /-
  #eval Nameless.Tm.infer_reduce 0 [lessterm| 
    let y[0] = fix (\ y[0] =>
      \ (#zero(), y[0]) => #true()  
      \ (#succ y[0], #succ y[1]) => (y[2] (y[0], y[1])) 
      \ (#succ y[0], #zero()) => #false() 
    ) in
    let y[0] = (\ (y[0], y[1]) => 
      (
        (
        \ #true() => y[1]
        \ #false() => y[0]
        )
        (y[2] (y[0], y[1]))
      )
    ) in
    (y[0] (#succ #zero(), #succ #succ #succ #zero()))
    -- (y[0] (#succ #zero(), #zero()))
  ] 
  -/

  -- better: notions of ?zero and ?true appear in inferred type? 
  -- this requires including relational constraints in generalization
  -- this works! 
  #eval Nameless.Tm.infer_reduce 0 [lessterm| 
    (\ (y[0]) => ((fix (\ y[0] =>
      \ (#zero(), #zero()) => #true()  
    )) (y[0])))
  ] 

  -- expected: ?true unit
  #eval Nameless.Tm.infer_reduce 0 [lessterm| 
    let y[0] = (\ (y[0]) => ((fix (\ y[0] =>
      \ (#zero(), #zero()) => #true()  
    )) (y[0])))
    in
    (y[0] (#zero(), #zero()))
  ] 

  --------------- debugging ---------------

  -- expected: ?false unit 
  #eval Nameless.Tm.infer_reduce 0 [lessterm| 
    (
      (fix (\ y[0] =>
        \ (#zero(), y[0]) => #true()  
        \ (#succ y[0], #succ y[1]) => (y[2] (y[0], y[1])) 
        \ (#succ y[0], #zero()) => #false() 
      ))
      (#succ #succ #zero(), #succ #zero())
    )
  ] 

  #eval Nameless.Tm.infer_reduce 0 [lessterm| 
    let y[0] = (fix (\ y[0] =>
      \ (#zero(), y[0]) => #true()  
      \ (#succ y[0], #succ y[1]) => (y[2] (y[0], y[1])) 
      \ (#succ y[0], #zero()) => #false() 
    )) in
    (y[0] (#succ #succ #zero(), #succ #zero()))
  ] 

  #eval Nameless.Tm.infer_reduce 0 [lessterm| 
    (fix (\ y[0] =>
      \ (#zero(), y[0]) => #true()  
      \ (#succ y[0], #succ y[1]) => (y[2] (y[0], y[1])) 
      \ (#succ y[0], #zero()) => #false() 
    ))
  ] 



  #eval Nameless.Ty.unify_decide 10 
  [lesstype| ?succ ?zero unit * ?zero unit]
  nat_pair


  def le_ := [lesstype|
    induct
      {(?zero unit * β[0]) * ?true unit} 
      | 
      {(?succ β[0] * ?succ β[1]) * β[2] with (β[0] * β[1]) * β[2] <: β[3] } 
      | 
      {(?succ β[0] * ?zero unit) * ?false unit}
  ]

  -- expected: ⊥ 
  #eval Nameless.Ty.unify_reduce 10 
  [lesstype|
    (forall [1] β[0] <: ?ooga unit 
       have (β[0] ->
    {[1] β[0] with (β[1] * β[0]) <: ⟨le_⟩}))
  ]
  [lesstype| ?succ ?succ ?zero unit * ?succ ?zero unit -> α[0]]
  [lesstype| α[0] ]

  -- expected: ?false unit 
  #eval Nameless.Ty.unify_reduce 10 
  [lesstype|
    (forall [1] β[0] <: ⟨nat_pair⟩ 
       have (β[0] ->
    {[1] β[0] with (β[1] * β[0]) <: ⟨le_⟩}))
  ]
  [lesstype| ?succ ?succ ?zero unit * ?succ ?zero unit -> α[0]]
  [lesstype| α[0] ]

  ----------------------------
  -- incomplete without model-based subtyping
  ----------------------------
  -- URL: https://pnwamk.github.io/sst-tutorial/#%28part._sec~3asemantic-subtyping%29
  #eval Nameless.Ty.unify_decide 0
  [lesstype| (?x unit | ?y unit) * ?y unit ] 
  [lesstype| (?x unit * ?y unit) | (?y unit * ?y unit) ] 

  -------------------------