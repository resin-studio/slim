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

  -- TODO: rewrite using natural recursion, which might better for automatic termination
  def bind_nl (i_xs : Nat × List α) 
    (f : Nat -> α -> (Nat × List β)) 
  : (Nat × List β) 
  :=
    let (i, xs) := i_xs
    List.foldl (fun (i, u_acc) env_ty =>
      let (i, xs) := (f i env_ty)
      (i, u_acc ++ xs)
    ) (i, []) xs 


  def all_nl (i_xs : Nat × List α) 
    (f : Nat -> α -> (Nat × List β)) 
  : (Nat × List β) 
  := 
    let (i, xs) := i_xs

    if !xs.isEmpty then
      let op := xs.foldl (fun op_acc x =>
        match op_acc with
        | none => none
        | some (i, acc) => (
          let (i, acc') := f i x
          if acc'.isEmpty then
            none
          else
            some (i, acc ++ acc')
        )
      ) (some (i, []))

      match op with
      | some result => result
      | none => (i, [])
    else 
      (i, [])

  #eval bind_nl (0, [1,2,3]) (fun i x => (i, [x]))

  #check List.mapM
  #check List.bind
  #eval [1,2,3].mapM (fun i => if i % 2 == 0 then some [i + 1] else none)
  #eval [2,4,6].mapM (fun i => if i % 2 == 0 then some [i + 1] else none)


  -- TODO: generalize form of constraints to allow a set of mutually dependent subtypings 
  -- TODO: remove calls to unify in infer; simply generate constraints 
  -- TODO: remove descriptive flags from type inference. 
    -- staged solving offloads the semantics of descriptive flags to a different constraint solving strategy.
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
  | impli : Ty -> Ty -> Ty
  /- payload -> List (lower <: upper) -> bound -> Ty -/
  | exis : Ty -> List (Ty × Ty) -> Nat -> Ty
  -- TODO: remove Option from univ; top type is sufficient
  | univ : Option Ty -> Ty -> Ty
  | induc : Ty -> Ty
  | coduc : Ty -> Ty
  deriving Repr, Inhabited, Hashable, BEq
  -- #check List.repr

  namespace Ty

    structure Qual where
      -- type variable qualifiers are top-down directed 
      -- top-down is sufficienct if flag is introduced when variable is introduced  
      -- if the flag were introduced at first usage of variable, 
        -- then top-down would be insufficient.
        --  and the flag would need to propagate bottom-up and left-to-right
      descrip : PHashSet Nat -- used to control adjustment

    def adjustable (q : Qual) (id : Nat) : Bool :=
      q.descrip.contains id

    structure Context where
      -- invariant: simple_to_relational.contains key --> 
      --              exsists ty_lower , ty_lower == simple_to_relational.find key  && env_relational.contains ty_lower   
      env_simple : PHashMap Nat Ty
      env_keychain : PHashMap Nat (PHashSet Ty)
      env_relational : PHashMap Ty Ty
      -- adj : PHashSet Nat
    deriving Repr

    instance : BEq Context where
      beq a b := a.env_simple.toList == b.env_simple.toList

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
    | .impli ty1 ty2 =>
      let n1 := infer_abstraction start ty1 
      let n2 := infer_abstraction start ty2
      if n1 > n2 then n1 else n2 
    | .exis payload constraints n =>
      let rec loop : List (Ty × Ty) -> Nat
      | [] => 0 
      | (ty_c1, ty_c2) :: constraints => 
        let m := loop constraints
        let n_c1 := infer_abstraction (start + n) ty_c1 
        let n_c2 := infer_abstraction (start + n) ty_c2
        Nat.max m (Nat.max n_c1 n_c2)
      let m := loop constraints
      let n_pl := infer_abstraction (start + n) payload  
      Nat.max m n_pl 
    | .univ op_ty_c ty_pl =>
      let n_c := match op_ty_c with 
      | some ty_c => infer_abstraction (start + 1) ty_c 
      | none => 0
      let n_pl := infer_abstraction (start + 1) ty_pl  
      Nat.max n_c n_pl
    | .induc content =>
      infer_abstraction (start + 1) content 
    | .coduc content =>
      infer_abstraction (start + 1) content 

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
    | .impli ty1 ty2 => (free_vars ty1).fold insert (free_vars ty2)
    | .exis ty constraints n =>
      constraints.foldl (fun total (ty_c1, ty_c2) =>
        total + (free_vars ty_c1) + (free_vars ty_c2)
      ) (free_vars ty)
    | .univ op_ty_c ty =>
      match op_ty_c with
      | some ty_c => (free_vars ty_c) + (free_vars ty)
      | none => (free_vars ty)
    | .induc ty => (free_vars ty)
    | .coduc ty => (free_vars ty)

    -- def neg_vars (neg : Bool) : Ty -> PHashSet Nat 
    -- | .bvar id => empty 
    -- | .fvar id => 
    --   if neg then
    --     empty.insert id
    --   else
    --     empty
    -- | .unit => empty 
    -- | .top => empty 
    -- | .bot => empty 
    -- | .tag l ty => (neg_vars neg ty) 
    -- | .field l ty => (neg_vars neg ty)
    -- | .union ty1 ty2 => (neg_vars neg ty1).fold insert (neg_vars neg ty2)
    -- | .inter ty1 ty2 => (neg_vars neg ty1).fold insert (neg_vars neg ty2)
    -- | .impli ty1 ty2 => (neg_vars true ty1).fold insert (neg_vars neg ty2)
    -- | .exis n ty_c1 ty_c2 ty =>
    --   (neg_vars neg ty_c1) + (neg_vars neg ty_c2) + (neg_vars neg ty)
    -- | .univ op_ty_c ty =>
    --   match op_ty_c with
    --   | some ty_c => (neg_vars neg ty_c) + (neg_vars neg ty)
    --   | none => (neg_vars neg ty)
    -- | .induc ty => (neg_vars neg ty)

    partial def abstract (fids : List Nat) (start : Nat) : Ty -> Ty
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
    | .impli ty1 ty2 => .impli (abstract fids start ty1) (abstract fids start ty2)
    | .exis ty constraints n => 
      let constraints' := constraints.map (fun (ty_c1, ty_c2) =>
        (abstract fids (start + n) ty_c1, abstract fids (start + n) ty_c2)
      )
      (.exis (abstract fids (start + n) ty) constraints' n)
    | .univ op_ty_c ty => 
      (.univ (Option.map (abstract fids (start + 1)) op_ty_c) (abstract fids (start + 1) ty))
    | .induc ty => .induc (abstract fids (start + 1) ty)
    | .coduc ty => .coduc (abstract fids (start + 1) ty)

    -- assuming no cycles; (assuming occurs check has been properly applied before hand) 
    partial def subst (m : PHashMap Nat Ty) : Ty -> Ty
    | .bvar id => .bvar id 
    | .fvar id => (match m.find? id with
      | some ty => 
        subst m ty 
      | none => .fvar id
    )
    | .unit => .unit
    | .top => .top
    | .bot => .bot
    | .tag l ty => .tag l (subst m ty) 
    | .field l ty => .field l (subst m ty)
    | .union ty1 ty2 => .union (subst m ty1) (subst m ty2)
    | .inter ty1 ty2 => .inter (subst m ty1) (subst m ty2)
    | .impli ty1 ty2 => .impli (subst m ty1) (subst m ty2)
    | .exis ty constraints n => 
      let constraints' := constraints.map (fun (ty_c1, ty_c2) =>
        (subst m ty_c1, subst m ty_c2)
      )
      (.exis (subst m ty) constraints' n)
    | .univ op_ty_c ty => 
      (.univ (op_ty_c.map (subst m)) (subst m ty))
    | .induc ty => .induc (subst m ty)
    | .coduc ty => .coduc (subst m ty)

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

    def intersect_over (f : (Ty × Ty) -> Ty) (constraints : List (Ty × Ty)) : Ty :=
      (constraints.foldr (fun (lhs, rhs) ty_acc =>
        intersect (f (lhs, rhs)) ty_acc 
      ) Ty.top)

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
    | .impli ty1 ty2 => .impli (simplify ty1) (simplify ty2)
    | .exis ty constraints n=> 
      let constraints' := constraints.map (fun (ty_c1, ty_c2) => 
        (simplify ty_c1, simplify ty_c2) 
      )
      .exis (simplify ty) constraints' n
    | .univ op_ty_c ty => 
      .univ (op_ty_c.map simplify) (simplify ty)
    | .induc ty => .induc (simplify ty)
    | .coduc ty => .coduc (simplify ty)


    def record_fields : Ty -> PHashMap String Ty
    | .field l ty => empty.insert l ty
    | .inter (.field l ty1) ty2 => 
      let linear_ty2 := (record_fields ty2) 
      match linear_ty2.find? l with
      | some ty_old => linear_ty2.insert l (Ty.inter ty1 ty_old)
      | none => linear_ty2.insert l ty1
    | .inter ty1 (.field l ty2) => 
      let linear_ty1 := (record_fields ty1)
      match linear_ty1.find? l with
      | some ty_old => linear_ty1.insert l (Ty.inter ty2 ty_old)
      | none => linear_ty1.insert l ty2
    | _ => empty 

    partial def wellformed_key : Ty -> Bool
    | .bvar id => false 
    | .fvar id => true 
    | .unit => false 
    | .top => false 
    | .bot => false 
    | .tag l ty => (wellformed_key ty) 
    | .field l ty => (wellformed_key ty)
    | .union ty1 ty2 => false 
    | .inter ty1 ty2 => 
      let fields := (record_fields (.inter ty1 ty2)).toList
      fields.all (fun (l, ty) => wellformed_key ty)
    | .impli ty1 ty2 => false 
    | .exis ty constraints n => false
    | .univ op_ty_c ty => false
    | .induc ty => false
    | .coduc ty => false

    partial def subst_while (f : Ty -> Bool) (m : PHashMap Nat Ty) : Ty -> Ty
    | .bvar id => .bvar id 
    | .fvar id => (match m.find? id with
      | some ty => 
        let ty := simplify ty
        if f ty then
          subst_while f m ty 
        else
          .fvar id
      | none => .fvar id
    )
    | .unit => .unit
    | .top => .top
    | .bot => .bot
    | .tag l ty => .tag l (subst_while f m ty) 
    | .field l ty => .field l (subst_while f m ty)
    | .union ty1 ty2 => .union (subst_while f m ty1) (subst_while f m ty2)
    | .inter ty1 ty2 => .inter (subst_while f m ty1) (subst_while f m ty2)
    | .impli ty1 ty2 => .impli (subst_while f m ty1) (subst_while f m ty2)
    | .exis ty constraints n => 
      let constraints' := constraints.map (fun (ty_c1, ty_c2) =>
        (subst_while f m ty_c1, subst_while f m ty_c2)
      )
      (.exis (subst_while f m ty) constraints' n)
    | .univ op_ty_c ty => 
      (.univ (op_ty_c.map (subst_while f m)) (subst_while f m ty))
    | .induc ty => .induc (subst_while f m ty)
    | .coduc ty => .coduc (subst_while f m ty)

    partial def sub_nonneg (stale : PHashSet Nat) (m : PHashMap Nat Ty) (negs : PHashSet Nat) : Ty -> Ty
    | .bvar id => .bvar id 
    | .fvar id => 
      if !stale.contains id && negs.contains id then
        (match m.find? id with
          | some ty => 
            sub_nonneg stale m negs ty 
          | none => .fvar id
        )
      else .fvar id 
    | .unit => .unit
    | .top => .top
    | .bot => .bot
    | .tag l ty => .tag l (sub_nonneg stale m negs ty) 
    | .field l ty => .field l (sub_nonneg stale m negs ty)
    | .union ty1 ty2 => .union (sub_nonneg stale m negs ty1) (sub_nonneg stale m negs ty2)
    | .inter ty1 ty2 => .inter (sub_nonneg stale m negs ty1) (sub_nonneg stale m negs ty2)
    | .impli ty1 ty2 => 
      let new_negs := free_vars ty1
      .impli ty1 (sub_nonneg stale m (negs + new_negs) ty2)
    | .exis ty constraints n => 
      let constraints' := constraints.map (fun (ty_c1, ty_c2) => 
        (sub_nonneg stale m negs ty_c1, sub_nonneg stale m negs ty_c2) 
      )
      (.exis (sub_nonneg stale m negs ty) constraints' n)
    | .univ op_ty_c ty => 
      (.univ (op_ty_c.map (sub_nonneg stale m negs)) (sub_nonneg stale m negs ty))
    | .induc ty => .induc (sub_nonneg stale m negs ty)
    | .coduc ty => .coduc (sub_nonneg stale m negs ty)


    declare_syntax_cat lesstype


    syntax:90 num : lesstype 
    syntax:90 ident : lesstype
    syntax:90 "β["lesstype"]" : lesstype
    syntax:90 "α["lesstype"]" : lesstype
    syntax:90 "unit" : lesstype
    syntax:90 "top" : lesstype
    syntax:90 "bot" : lesstype
    syntax:80 lesstype:81 "//" lesstype:80 : lesstype
    syntax:80 lesstype:81 ":" lesstype:80 : lesstype
    syntax:70 lesstype:71 "&" lesstype:70 : lesstype
    syntax:70 lesstype:71 "*" lesstype:70 : lesstype
    syntax:60 lesstype:61 "|" lesstype:60 : lesstype
    syntax:50 lesstype:51 "->" lesstype:50 : lesstype


    -- constraints
    syntax:40 lesstype "<:" lesstype : lesstype
    syntax:40 lesstype "<:" lesstype "," lesstype: lesstype
    ------------

    syntax "{" lesstype:41 "with" lesstype "#" lesstype "}": lesstype 
    syntax "{" lesstype:41 "#" lesstype "}" : lesstype 

    syntax "{" lesstype:41 "with" lesstype "}": lesstype 
    syntax "{" lesstype:41 "}" : lesstype 

    -- TODO: update bound quantification with subtyping symbol <:
    syntax:50 "[" "_" "<:" lesstype:51 "]" lesstype:50 : lesstype 
    syntax:50 "[" "_" "]" lesstype:50 : lesstype 

    syntax "induct" lesstype:40 : lesstype 
    syntax "coduct" lesstype:40 : lesstype 

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
    | `([lesstype| top ]) => `(Ty.top)
    | `([lesstype| bot ]) => `(Ty.bot)
    | `([lesstype| $a // $b:lesstype ]) => `(Ty.tag [lesstype| $a ] [lesstype| $b ])
    | `([lesstype| $a : $b:lesstype ]) => `(Ty.field [lesstype| $a ] [lesstype| $b ])
    | `([lesstype| $a -> $b ]) => `(Ty.impli [lesstype| $a ] [lesstype| $b ])
    | `([lesstype| $a | $b ]) => `(Ty.union [lesstype| $a ] [lesstype| $b ])
    | `([lesstype| $a & $b ]) => `(Ty.inter [lesstype| $a ] [lesstype| $b ])
    | `([lesstype| $a * $b ]) => `(Ty.inter (Ty.field "l" [lesstype| $a ]) (Ty.field "r" [lesstype| $b ]))


    -- constraints
    | `([lesstype| $b <: $c  ]) => `([([lesstype| $b ],[lesstype| $c ])])
    | `([lesstype| $b <: $c , $xs ]) => `(([lesstype| $b ],[lesstype| $c ]) :: [lesstype| $xs])
    --------------

    | `([lesstype| { $d with $xs # $n}  ]) => 
      `(Ty.exis [lesstype| $d ] [lesstype| $xs ] [lesstype| $n ])

    | `([lesstype| { $b:lesstype # $n } ]) => `(Ty.exis [lesstype| $b ] [] [lesstype| $n ] )

    | `([lesstype| { $d with $xs}  ]) => 
      `(Ty.exis [lesstype| $d ] [lesstype| $xs ] (Ty.infer_abstraction 0 [lesstype| $d ]))

    | `([lesstype| { $b:lesstype } ]) => 
      `(Ty.exis (Ty.infer_abstraction 0 [lesstype| $b ]) [] [lesstype| $b ] )

    | `([lesstype| [ _ ] $d  ]) => 
      `(Ty.univ none [lesstype| $d ])

    | `([lesstype| [ _ <: $a ] $d  ]) => 
      `(Ty.univ (some [lesstype| $a ]) [lesstype| $d ])

    | `([lesstype| induct $a ]) => `(Ty.induc [lesstype| $a ])
    | `([lesstype| coduct $a ]) => `(Ty.coduc [lesstype| $a ])

    | `([lesstype| ($a) ]) => `([lesstype| $a ])

    | `([lesstype| ⟨ $e ⟩ ]) => pure e


    partial def repr (ty : Ty) (n : Nat) : Format :=
    match ty with
    | .bvar id => 
      "β[" ++ Nat.repr id ++ "]"
    | .fvar id =>
      "α[" ++ Nat.repr id ++ "]"
    | .unit => "unit" 
    | .top => "top" 
    | .bot => "bot" 
    | .tag l ty1 => 
      (l ++ "//" ++ (repr ty1 n))
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
    | .impli ty1 ty2 =>
      Format.bracket "(" ((repr ty1 n) ++ " ->" ++ Format.line ++ (repr ty2 n)) ")"
    | .exis ty_pl constraints var_count =>
      if constraints.isEmpty then
        Format.bracket "{" (
          repr ty_pl n ++
          " # " ++ (Nat.repr var_count)
        ) "}"
      else
        let constraints' := constraints.map (fun (ty_c1, ty_c2) =>
          (repr ty_c1 n) ++ " <: " ++ (repr ty_c2 n)
        )
        let constraints'' := Format.joinSep constraints' ", "
        Format.bracket "{" (
          (repr ty_pl n) ++ " with " ++
          constraints'' ++
          " # " ++ (Nat.repr var_count)
        ) "}"
    | .univ op_ty_c ty_pl =>
      match op_ty_c with
      | none =>
        Format.bracket "(" ("[_]" ++ (repr ty_pl n)) ")"
      | some ty_c =>
        Format.bracket "(" (
          "[_:" ++ (repr ty_c n) ++ "]" ++ (repr ty_pl n)
        ) ")"
    | .induc ty1 =>
      Format.bracket "(" (
        "induct " ++ (repr ty1 n)
      ) ")"
    | .coduc ty1 =>
      Format.bracket "(" (
        "coduct " ++ (repr ty1 n)
      ) ")"

    instance : Repr Ty where
      reprPrec := repr

    instance : ToString Ty where
      toString := fun t => Format.pretty (repr t 0)

  #check Format
  def envRepr 
  (m : PHashMap Nat Ty) (n : Nat) : Format :=
    let xs : List Format := (toList m).map (fun (k, v) => (Nat.repr k) ++ " ↦ " ++ (Ty.repr v n))
    let contents : Format := xs.foldl (fun acc item =>
      acc ++ "  " ++ item ++ ",\n"
    ) "\n" 
    Format.bracket "{" contents "}"

  instance : Repr (PHashMap Nat Ty) where
    reprPrec := envRepr


  -- def PHashSet.repr [Repr α] [BEq α] [Hashable α] 
  -- (m : PHashSet α) (n : Nat) : Format :=
  --   Format.bracket "{" (List.repr (toList m) n) "}"

  -- instance [Repr α] [BEq α] [Hashable α] : Repr (PHashSet α) where
  --   reprPrec := PHashSet.repr

------------------------------------------------------------

    #eval [lesstype| {β[0] with β[0] <: ooga//unit, β[0] <: booga//unit} ]
    #eval [lesstype| {β[0] with β[0] <: ooga//unit} ]

    #eval [lesstype| {β[0] with (β[1] * β[0]) <: booga//unit # 1} ] 
    #eval [lesstype| {β[0] with β[1] * β[0] <: booga//unit # 1} ] 
    #eval [lesstype| [_ <: ooga//unit] β[0] -> {β[0] with β[1] * β[0] <: booga//unit # 1} ] 

------------------------------------------------------------


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
    | .impli _ _ => false
    | .exis ty_pl constraints n =>
      /-
      NOTE: Lean can't automatically prove termination using higher order function in this particular case
      -/
      -- (no_function_types ty_pl) && constraints.all (fun (ty_c1, ty_c2) => 
      --   (no_function_types ty_c1) && (no_function_types ty_c2)
      -- )
      let rec loop : List (Ty × Ty) -> Bool  
      | [] => true
      | (ty_c1, ty_c2) :: constraints => 
        (loop constraints) && 
        (no_function_types ty_c1) && (no_function_types ty_c2)

      (no_function_types ty_pl) && (loop constraints)

    | .univ op_ty_c ty_pl =>
      (match op_ty_c with 
      | none => true
      | some ty_c => no_function_types ty_c
      ) && 
      no_function_types ty_pl
    | .induc content => no_function_types content 
    | .coduc content => no_function_types content 

    partial def index_free_vars (initial : PHashMap Nat (PHashSet Ty)) (ty : Ty) : PHashMap Nat (PHashSet Ty) :=
      let fids := toList (free_vars ty)
      fids.foldl (fun acc fid =>
        match acc.find? fid with
        | some keys => 
          if keys.contains ty then 
            acc
          else
            acc.insert fid (keys.insert ty)
        | none => acc.insert fid (empty.insert ty)
      ) initial 


      ---------------------------------------
      -- let constraints_acc := (
      --     if constraints_acc.contains (Ty.fvar fid) then
      --       match context.env_simple.find? fid with
      --       | some ty_simple =>
      --         let constraints_acc := constraints_acc.insert (Ty.fvar fid) ty_simple 
      --         (reachable_constraints context ty_simple constraints_acc)
      --       | none => constraints_acc
      --     else
      --       constraints_acc
      -- )
      -------------------------------------------

    partial def reachable_constraints (context : Context) (ty : Ty) (constraints_acc : PHashMap Ty Ty) : PHashMap Ty Ty :=
      (free_vars ty).fold (fun constraints_acc fid =>
        let constraints_acc := (
          match context.env_keychain.find? fid with
          | some keychain =>
            keychain.fold (fun constraints_acc key =>
              if constraints_acc.contains key then
                constraints_acc
              else
                (match context.env_relational.find? key with
                | some relation => 
                  let constraints_acc := constraints_acc.insert key relation 
                  (reachable_constraints context relation constraints_acc)
                | none => 
                  -- invariant: this impli should never happen
                  constraints_acc 
                )
            ) constraints_acc
          | none => constraints_acc
        )
        constraints_acc 
      ) constraints_acc


    -- deprecated
    -- partial def pack (stale : PHashSet Nat) (context : Context) (negs : PHashSet Nat) (ty : Ty) :=
    --   -----------------------
    --   -- assumption: env_simple is cycle-free  
    --   -- keep variables that exist in parameter position; substitute variables that are only in return position 
    --   -- avoid substitution to allow constraint refinements
    --   -- recursively pack referenced variables as constraints
    --   -----------------------

    --   let ty := sub_nonneg stale context.env_simple negs ty

    --   let fids := (free_vars ty)
    --   if fids.isEmpty then
    --     ty
    --   else 

    --     let constraints : PHashMap Ty Ty := empty

    --     -- simple constraints
    --     let constraints : PHashMap Ty Ty := fids.fold (fun constraints fid =>
    --       if !stale.contains fid then
    --         match context.env_simple.find? fid with
    --         | some ty_simple =>
    --           constraints.insert (Ty.fvar fid) (pack stale context (negs + fids) ty_simple) 
    --         | none => constraints
    --       else
    --         constraints
    --     ) constraints 

    --     -- relational constraints
    --     let constraints : PHashMap Ty Ty := fids.fold (fun constraints fid => 
    --       if !stale.contains fid then
    --         match context.env_keychain.find? fid with
    --         | some keychain =>
    --           keychain.fold (fun constraints key =>
    --             (match context.env_relational.find? key with
    --             | some relation => 
    --               let key := sub_nonneg stale context.env_simple (negs + fids) key
    --               if constraints.contains key then
    --                 constraints
    --               else
    --                 constraints.insert key (pack stale context (negs + fids) relation) 
    --             | none => 
    --               -- invariant: this impli should never happen
    --               constraints 
    --             )
    --           ) constraints
    --         | none => constraints
    --       else
    --         constraints
    --     ) constraints 


    --     if constraints.isEmpty then
    --       let list_fids := toList fids
    --       [lesstype| {⟨list_fids.length⟩ // ⟨abstract list_fids 0 ty⟩}  ]
    --     else
    --       intersect_over (fun (ty_lhs, ty_rhs) => 
    --         let fvs_constraints := fids + (free_vars ty_lhs) + (free_vars ty_rhs)
    --         let fids_c := List.filter (fun id => !stale.contains id) (toList fvs_constraints)
    --         [lesstype|
    --           {⟨fids_c.length⟩ // ⟨abstract fids_c 0 ty⟩ with ⟨abstract fids_c 0 ty_lhs⟩ <: ⟨abstract fids_c 0 ty_rhs⟩}
    --         ]
    --       ) constraints.toList





    partial def instantiate (start : Nat) (args : List Ty) : Ty -> Ty
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
    | .impli ty1 ty2 => .impli (instantiate start args ty1) (instantiate start args ty2)
    | .exis ty constraints n => 
      let constraints' := constraints.map (fun (ty_c1, ty_c2) =>
        (instantiate (start + n) args ty_c1, instantiate (start + n) args ty_c2)
      )
      (.exis (instantiate (start + n) args ty) constraints' n)
    | .univ op_ty_c ty => 
      (.univ (Option.map (instantiate (start + 1) args) op_ty_c) (instantiate (start + 1) args ty)
      )
    | .induc ty => .induc (instantiate (start + 1) args ty)
    | .coduc ty => .coduc (instantiate (start + 1) args ty)


    partial def occurs (m : Ty.Context) (key : Nat): Ty -> Bool 
    | .bvar id => false 
    | .fvar id => 
      (key == id) || 
      (match m.env_simple.find? id with
      | some ty => occurs m key ty 
      | none => 
        (match m.env_keychain.find? id with
        | some keychain => 
          (toList keychain).any (fun lower => 
            (match m.env_relational.find? lower with
            | some relation => occurs m key relation 
            | none => false
            )
          )
        | none => false
        )
      )
    | .unit => false 

    | .top => false 
    | .bot => false 
    | .tag l ty => occurs m key ty 
    | .field l ty => occurs m key ty
    | .union ty1 ty2 => (occurs m key ty1) || (occurs m key ty2)
    | .inter ty1 ty2 => (occurs m key ty1) || (occurs m key ty2)
    | .impli ty1 ty2 => (occurs m key ty1) || (occurs m key ty2)
    | .exis ty constraints n => 
      (occurs m key ty) || (constraints.any (fun (ty_c1, ty_c2) =>
        (occurs m key ty_c1) || (occurs m key ty_c2)
      ))

    | .univ op_ty_c ty => 
      (match op_ty_c with
      | none => false
      | some ty_c => (occurs m key ty_c)) || (occurs m key ty)
    | .induc ty => (occurs m key ty)
    | .coduc ty => (occurs m key ty)

    partial def subst_default (sign : Bool) : Ty -> Ty
    | .bvar id => .bvar id  
    | .fvar id => if sign then .bot else .top 
    | .unit => .unit 
    | .top => .top
    | .bot => .bot 
    | .tag l ty => .tag l (subst_default sign ty) 
    | .field l ty => .field l (subst_default sign ty) 
    | .union ty1 ty2 =>
      .union (subst_default sign ty1) (subst_default sign ty2)
    | .inter ty1 ty2 =>
      .inter (subst_default sign ty1) (subst_default sign ty2)
    | .impli ty1 ty2 => .impli (subst_default (!sign) ty1) (subst_default sign ty2)
    | .exis ty constraints n => 
      -- can't sub away if constrained
      .exis ty constraints n
    | .univ op_ty_c ty => 
      -- can't sub away if constrained
      .univ op_ty_c ty
    | .induc ty => .induc (subst_default sign ty)
    | .coduc ty => .coduc (subst_default sign ty)

    partial def equiv (env_ty : PHashMap Nat Ty) (ty1 : Ty) (ty2 : Ty) : Bool :=
      let ty1 := simplify (subst env_ty ty1)
      let ty2 := simplify (subst env_ty ty2)
      ty1 == ty2

    def split_intersections : Ty -> List Ty 
    | Ty.inter ty1 ty2 =>
      (split_intersections ty1) ++ (split_intersections ty2)
    | ty => [ty]

    def split_unions : Ty -> List Ty 
    | Ty.union ty1 ty2 =>
      (split_unions ty1) ++ (split_unions ty2)
    | ty => [ty]

    -- def linearize_fields : Ty -> Option (List (String × Ty))
    -- | .field l ty => some [(l, ty)]
    -- | .inter (.field l ty1) ty2 => 
    --   bind (linearize_fields ty2) (fun linear_ty2 =>
    --     (l, ty1) :: linear_ty2
    --   )
    -- | .inter ty1 (.field l ty2) => 
    --   bind (linearize_fields ty1) (fun linear_ty1 =>
    --     (l, ty2) :: linear_ty1
    --   )
    -- | .fvar _ => some [] 
    -- | _ => none

    -- def extract_nested_fields : Ty -> (List Ty)
    -- | .field l ty => [ty]
    -- | .inter (.field l ty1) ty2 => 
    --   match extract_nested_fields ty1 with
    --   | [] => ty1 :: (extract_nested_fields ty2)
    --   | nested_fields =>
    --     nested_fields ++ (extract_nested_fields ty2)
    -- | .inter ty1 (.field l ty2) => 
    --   match extract_nested_fields ty2 with
    --   | [] => ty2 :: (extract_nested_fields ty1)
    --   | nested_fields => nested_fields ++ (extract_nested_fields ty1)
    -- | _ => [] 


    partial def extract_record_labels : Ty -> PHashSet String
    | .field l ty => 
      empty.insert l
    | .union ty1 ty2 => 
      (extract_record_labels ty1) + (extract_record_labels ty2)
    | .inter ty1 ty2 => 
      let fields := toList (record_fields (Ty.inter ty1 ty2))
      from_list (fields.map (fun (l, _) => l))
    | .exis ty constraints n => (extract_record_labels ty)
    | .induc ty => extract_record_labels ty
    | .coduc ty => extract_record_labels ty
    | _ => {} 

    partial def extract_label_list (ty : Ty) : List String :=
      toList (extract_record_labels ty)

    def part_of_relational_key (context: Context) (key : Nat): Bool := 
      context.env_relational.toList.find? (fun (key_rel, _ ) =>
        let fids := free_vars key_rel
        fids.contains key
      ) != none

    def extract_field (label : String) (ty : Ty) : Option Ty := do
      let fields := toList (record_fields ty)
      let fields_filt := fields.filter (fun (l, _) => l == label)
      if h : fields_filt.length > 0 then
        let (_, ty_fd) := (fields_filt.get ⟨0, h⟩)
        some ty_fd
      else
        none

    def extract_field_induct (label : String): Ty -> Option Ty 
    | .exis ty [(.bvar id, ty_pl)] n => 
      -- assume β[n] is the inductive fixed point 
      if id == n then
        Option.bind (extract_field label ty) (fun ty => 
        Option.bind (extract_field label ty_pl) (fun ty_pl =>
          (Ty.exis ty [(.bvar id, ty_pl)] n)
        ))
      else 
        none
    | .exis ty_pl [] n => 
      Option.bind (extract_field label ty_pl) (fun ty_pl =>
        (Ty.exis ty_pl [] n)
      )
    | ty => extract_field label ty 


    partial def factor_out_map (labels : List String) : Ty -> PHashMap String Ty 
    | Ty.induc ty =>
      let unions := split_unions ty
      labels.foldl (fun acc label =>
        let ty_col := unions.foldr (fun ty_row ty_col =>
          match extract_field_induct label ty_row with
          | some ty_field => Ty.union ty_field ty_col 
          | none => Ty.top
        ) Ty.bot 
        acc.insert label (Ty.induc (Ty.simplify ty_col))
      ) empty 
    | _ => 
      empty

    partial def factor_out_relation (labels : List String) (ty : Ty) : Ty :=
      let fields := toList (factor_out_map labels ty)
      fields.foldr (fun (label, ty_rec) ty_acc =>
        Ty.inter (Ty.field label ty_rec) ty_acc 
      ) Ty.top

    -- | Ty.induc ty =>
    --   let unions := split_unions ty
    --   labels.foldr (fun label ty_acc =>
    --     let ty_col := unions.foldr (fun ty_row ty_col =>
    --       match extract_field_induct label ty_row with
    --       | some ty_field => Ty.union ty_field ty_col 
    --       | none => Ty.top
    --     ) Ty.bot 
    --     Ty.inter (Ty.field label (Ty.induc ty_col)) ty_acc 
    --   ) Ty.top
    -- | ty => 
    --   Ty.top
    --   -- let unions := split_unions ty
    --   -- labels.foldr (fun label ty_acc =>
    --   --   let ty_col := unions.foldr (fun ty_row ty_col =>
    --   --     match extract_field label ty_row with
    --   --     | some ty_field => Ty.union ty_field ty_col 
    --   --     | none => Ty.top
    --   --   ) Ty.bot 
    --   --   Ty.inter (Ty.field label ty_col) ty_acc 
    --   -- ) Ty.top



    partial def decreasing (id_induct : Nat) : Ty -> Bool
    | .bvar id => id != id_induct 
    | .fvar _ => true 
    | .unit => true 
    | .top => true 
    | .bot => true 
    | .tag _ _ => true 
    | .field _ ty => decreasing id_induct ty
    | .union ty1 ty2 =>
      decreasing id_induct ty1 && decreasing id_induct ty2
    | .inter ty1 ty2 =>
      decreasing id_induct ty1 && decreasing id_induct ty2
    | .impli _ _ => false
    | .exis ty' constraints n'=> 
      constraints.all (fun (ty_c1, ty_c2) =>
        match ty' with 
        | .tag _ _ => 
          decreasing (id_induct + n') ty_c1
        | _ =>
          decreasing (id_induct + n') ty_c1 &&
          decreasing (id_induct + n') ty_c2 && 
          decreasing (id_induct + n') ty'
      )
    | .univ _ _ => false 
    | .induc _ => false 
    | .coduc _ => false 

    -- (fun ty_u => 
    --   match ty_u with
    --   | (Ty.tag _ _) => true
    --   | Ty.exis _ _ _ (Ty.tag _ _) => true
    --   | _ => false
    -- )


    -- check that ty_rec is wellfounded with respect to reducible column in ty_key
    partial def reducible (context : Ty.Context) (ty_key ty_rec : Ty) : Bool :=
      let ty_key := simplify (subst context.env_simple ty_key)  
      let fields := record_fields ty_key
      if fields.isEmpty then
        match ty_key with
        | Ty.fvar _ => false
        | Ty.tag _ _ =>
          match ty_rec with
          | Ty.induc ty_body =>
            let unions := split_unions ty_body
            -- TODO: decreasing is too strict
            -- increasing can be fine too 
            -- only the the switch that controls branching must be decreasing
            unions.all (decreasing 0)
          | _ => false 
        | _ => false
      else
        -- for each label in ty_rec there is a label in keys
        let labels := toList (extract_record_labels ty_rec)
        let ty_factored := toList (factor_out_map labels ty_rec)
        ty_factored.any (fun (l, ty_rec) =>
          match fields.find? l with
          | some ty_key => reducible context ty_key ty_rec
          | none => false
        )  


    def merge_contexts (c1 c2 : Ty.Context) : Ty.Context :=
      {
        env_simple := c1.env_simple;c2.env_simple,
        env_keychain := c1.env_keychain;c2.env_keychain
        env_relational := c1.env_relational;c2.env_relational
        -- adj := c1.adj + c2.adj
      }



    def constraint_unchanged (id : Nat) (context : Ty.Context) (contexts' : List Ty.Context) : Bool :=  
      contexts'.all (fun context' => 
        context'.env_simple.find? id == context.env_simple.find? id &&
        match context.env_keychain.find? id, context'.env_keychain.find? id with
        | some kc, some kc' => kc'.fold (fun result key => result && kc.contains key) true
        | none, none => true 
        | _, _ => false
      )

    -- -- antecedent exisential
    -- | ty1, .impli (.exis n ty_c1 ty_c2 ty_pl) ty3 =>
    --   -- TODO: reconsider if this rule is needed 
    --   -- TODO: safety check
    --   -- NOTE: special impli to ensure that variables are instantiated before decomposition of lhs
    --   -- NOTE: this only works if variables are freed before variable assignment
    --   ------------------
    --   -- let ty2 := (.exis n ty_c1 ty_c2 ty_pl)
    --   -- let (i, ty2') := (i + 1, Ty.fvar i)
    --   -- bind_nl (unify i context ty1 (.impli ty2' ty3)) (fun i context =>
    --   --   (unify i context ty2 ty2')
    --   -- )
    --   ------------------------
    --   let ty_arg := (.exis n ty_c1 ty_c2 ty_pl)
    --   let (i, ty_arg') := (i + 1, Ty.fvar i)
    --   bind_nl (unify i context ty_arg ty_arg') (fun i context =>
    --     (unify i context ty1 (.impli ty_arg' ty3))
    --   )

    partial def unify (i : Nat) (qual : Qual) (context : Context) (ty_l ty_r : Ty) : (Nat × List Context) :=
    if ty_l == ty_r then (i, [context]) else
    match ty_l, ty_r with

    -- right variable
    | ty', .fvar id => 
      ----------------------
      -- NOTE: this executes before the left-variable on rule. in impli where ty' is also an unassgined variable, save as rhs maps to lhs. 
        -- Enables freed existential vars (rhs) to map to closed existential vars (lhs). 
      -- adjustment here records observed types; based on unioning fresh variable
      -- assymetrical mechanism, since free variables have the meaning of Top, and environment tracks upper bounds
      -- when the environment is packed as a constraint; it becomes id <: ty', so we need union to make id <: ty' | Top
      -- NAT <: X with X * _ <: NAT_LIST fails because NAT * _ <: NAT_LIST fails 
      -- zero//unit <: X with X * _ <: NAT_LIST succeeds because zero//unit * _ <: NAT_LIST succeeds 
      --------------------

      match context.env_simple.find? id with 
      | some ty => 
        let (i, contexts) := (unify i qual context ty' ty) 

        if !contexts.isEmpty then
          (i, contexts)
        else if (adjustable qual id) && (!occurs context id (Ty.union ty' ty)) then
          let context := {context with env_simple := context.env_simple.insert id (Ty.unionize ty' ty)}
          (i, [context])
        else
          (i, [])

        ----------------------------------------------

      | none => 
        --- check env_relational
        match context.env_keychain.find? id with
        | some keychain =>
          keychain.fold (fun (i, contexts) key =>
            bind_nl (i, contexts) (fun i context => 
              match context.env_relational.find? key with
              | some relation => 
                -- TODO: add occurs check
                let env_sub : PHashMap Nat Ty := empty.insert id ty'
                let ty_sub := subst env_sub key  
                let (i, contexts) := (unify i qual context ty_sub relation) 
                ------------
                if !contexts.isEmpty then
                  (i, contexts)
                else
                  -- check inhabitation of [id <: ty']{... * id *.... with ... * id *.... <: R}
                  -- corresponds to factoring relation
                  let labels := extract_label_list key 
                  let (i, contexts_oracle) := (unify i qual context ty_sub (factor_out_relation labels relation))
                  if !contexts_oracle.isEmpty then
                    (i, [context])
                  else
                    (i, [])
              | none => 
                -- invariant: this never happens
                (i, [])
            )
          ) (i, [context])
        | none => (
          if (Ty.fvar id) == ty' then
            (i, [context])
          -- else if (!writable qual id) then
          --   (i, [context])
          else if !occurs context id ty' then
            (i, [{context with env_simple := context.env_simple.insert id ty' }])
          else
            (i, [])
        )
      ---------------------------------------

    -- left variable
    | .fvar id, ty  => 
      ----------------------------
      -- adjustment updates the variable assignment to lower the upper bound 
      ---------------------------
      -- check env_simple first
      -- then check env_keychain
        -- check if the relational constraints can be solved 

      match context.env_simple.find? id with 
      | some ty' => 
        let (i, contexts) := (unify i qual context ty' ty)
        if !contexts.isEmpty then
          (i, contexts)
        else if (adjustable qual id) && (!occurs context id (Ty.inter ty ty')) then
          let context := {context with env_simple := context.env_simple.insert id (Ty.inter ty ty')}
          (i, [context])
        else
          (i, [])
      | none => 
        match context.env_keychain.find? id with
        | some keychain =>
          keychain.fold (fun (i, contexts) key =>
            bind_nl (i, contexts) (fun i context => 
            match context.env_relational.find? key with
            | some relation =>
                -- check that new constraint is weaker than relational constraint  
                -- weakening is only safe if the constraint is not over parameter type 
                -- assumption: relations do not constraintfunction parameter types
                -- TODO: add occurs check
                let env_sub : PHashMap Nat Ty := empty.insert id ty
                let ty_sub := subst env_sub key  
                let ty_weak := (
                  let fids := toList (free_vars ty_sub)
                  [lesstype| {⟨abstract fids 0 ty_sub⟩ # ⟨fids.length⟩} ] 
                )
                -- unify relational lhs and constructed relational rhs 
                let (i, contexts_oracle) := (unify i qual context relation ty_weak)

                if !contexts_oracle.isEmpty then
                  (i, [context])
                else if (occurs context id ty) then
                    (i, [])
                else (
                  -- TODO: add occurs check
                  let context := {context with env_simple := context.env_simple.insert id ty}
                  (i, [context])
                )
              -- opaque_wrap context id (fun context =>
              -- )
            | none => 
              -- invariant: this should never happen
              (i, [])
            )
          ) (i, [context])
        | none =>
          if (Ty.fvar id) == ty then
            (i, [context])
          -- else if (!writable qual id) then
          --   let context := {context with env_simple := context.env_simple.insert id ty}
          --   let context := {context with env_simple := context.env_simple.insert (2000 + id) (Ty.tag s!"minlocal_{qual.minlocal}" Ty.unit)}
          --   (i, [context])
          else if (!occurs context id ty) then
            let context := {context with env_simple := context.env_simple.insert id ty}
            (i, [context])
          else
            (i, [])

    -----------------------------------------------------

    -- left existential
    | .exis ty1 constraints n, ty2 => (
      let (i, ids_bound) := (i + n, (List.range n).map (fun j => i + j))

      let args := ids_bound.map (fun id => Ty.fvar id)
      let constraints := constraints.map (fun (ty_c1, ty_c2) =>
        let ty_c1 := instantiate 0 args ty_c1
        let ty_c2 := instantiate 0 args ty_c2
        (ty_c1, ty_c2)
      )
      let ty1 := instantiate 0 args ty1


      let env_simple_unchanged : List Ty.Context -> Option Ty.Context := (fun new_contexts => 
        match new_contexts with
        | [new_context] => 
          if new_context.env_simple.toList == context.env_simple.toList then
            some new_context
          else
            none
        | _ => none
      )

      let (i, contexts_constraint) := all_nl (i, constraints) (fun i (ty_c1, ty_c2) => 
        (unify i qual context ty_c1 ty_c2)
      )
      match env_simple_unchanged contexts_constraint with 
      | some context_constraint => 
        let (i, contexts) := (unify i qual context_constraint ty1 ty2) 
        -- ensure that opaque variables are not bound from payload unification
        let result_safe := ids_bound.all (fun id => constraint_unchanged id context_constraint contexts)
        if result_safe then
          (i, contexts)
        else
          (i, [])
      | none => 
        all_nl (i, contexts_constraint) (fun i context_constraint =>
          let (i, contexts') := (unify i qual context_constraint ty1 ty2)
          if !contexts'.isEmpty && (ids_bound.all (fun id => constraint_unchanged id context_constraint contexts')) then
            (i, contexts')
          else
            (i, [])
        )
    ) 

    -- right universal
    | ty1, .univ op_ty_c ty2  => (
      let id_bound := i
      let i := i + 1

      let args := [Ty.fvar id_bound]
      let op_ty_c := Option.map (instantiate 0 args) op_ty_c
      let ty2 := instantiate 0 args ty2


      let context := match op_ty_c with
      | none => context
      | some ty_c => {context with 
        -- TODO: add occurs check
        env_simple := context.env_simple.insert id_bound ty_c
      }

      let (i, contexts) := (unify i qual context ty1 ty2)
      let result_safe := constraint_unchanged id_bound context contexts
      if result_safe then
        (i, contexts)
      else
        (i, [])
      -----------------------------
    )


    -- left induction
    | .induc ty, ty_r => 
      if equiv context.env_simple (.induc ty) (ty_r) then
        (i, [context])
      else
        let labels := extract_label_list ty_r
        let ty_factored := (factor_out_relation labels (.induc ty))
        let (i, contexts) := unify i qual context ty_factored ty_r
        if !contexts.isEmpty then
          (i, contexts)
        else
          -- using induction hypothesis, ty1 ≤ ty2; safely unroll
          let ty := instantiate 0 [ty_r] ty
          unify i qual context ty ty_r

    -- antecedent union 
    | ty1, .impli (Ty.union ty_u1 ty_u2) ty2 =>
      bind_nl (unify i qual context ty1 (Ty.impli ty_u1 ty2)) (fun i context =>
        unify i qual context ty1 (Ty.impli ty_u2 ty2)
      )

    -- consequent intersection
    | ty1, .impli ty2 (Ty.inter ty_u1 ty_u2) =>
      bind_nl (unify i qual context ty1 (Ty.impli ty2 ty_u1)) (fun i context =>
        unify i qual context ty1 (Ty.impli ty2 ty_u2)
      )

    -- left union
    | Ty.union ty1 ty2, ty => 
      bind_nl (unify i qual context ty1 ty) (fun i context =>
        (unify i qual context ty2 ty)
      )

    -- right intersection
    | ty, .inter ty1 ty2 => 
      bind_nl (unify i qual context ty ty1) (fun i context =>
        (unify i qual context ty ty2)
      )


    ---------------------------------------------------

    -- right existential
    | ty', .exis ty constraints n =>
      let (i, args) := (
        i + n, 
        (List.range n).map (fun j => Ty.fvar (i + j))
      )

      let constraints := constraints.map (fun (ty_c1, ty_c2) => 
        let ty_c1 := instantiate 0 args ty_c1
        let ty_c2 := instantiate 0 args ty_c2
        (ty_c1, ty_c2)
      ) 
      let ty := instantiate 0 args ty

      -------------------
      -- try backtracking order first
      -- NOTE: unify constraint last, as quantified variables should react to unification of payloads
      -------------------
      let (i, contexts) := (
        --------------
        -- backwards
        --------------
        bind_nl (unify i qual context ty' ty) (fun i context => 
          all_nl (i, constraints) (fun i (ty_c1, ty_c2) =>
            unify i qual context ty_c1 ty_c2
          )
        )
      )

      if !contexts.isEmpty then
        (i, contexts)
      else
        (i, [])
        --------------
        -- forward 
        -- diverges
        --------------
        -- bind_nl (unify i context ty_c1 ty_c2) (fun i context => 
        --   unify i context ty' ty
        -- )
        ---------------


    -- left universal
    | .univ op_ty_c ty1, ty2 =>
      let (i, id_bound) := (i + 1, i)
      let args := [Ty.fvar id_bound]

      let op_ty_c := Option.map (instantiate 0 args) op_ty_c
      let ty1 := instantiate 0 args ty1

      ----------------------------
      -- try both orders: forward and backtracking;
      -- only necessary that some solution exists 
      ----------------------------
      -- backtracking
      -- NOTE: unify constraint last, as quantified variables should react to unification of payloads
      ----------------------------
      let (i, contexts) := (
        bind_nl (unify i qual context ty1 ty2) (fun i context => 
          match op_ty_c with
          | none => (i, [context])
          | some ty_c => (
            -------------------------------------
            let op_ty_b := context.env_simple.find? id_bound 
            match op_ty_b with
            | some ty_b => 
              (unify i qual context ty_b ty_c)
            | none => 
              -- TODO: add occurs check
              (i, [{context with env_simple := context.env_simple.insert id_bound ty_c}])
          )
        )
      )
      -- TODO: could union solutions together instead of if/else
      if !contexts.isEmpty then
        (i, contexts)
      else 
        -----------------------------------------
        -- forward tracking
        -- This allows more complete subtyping, but breaks relational selection 
        -- consider a mechanism that combines both directions
        -----------------------------------------
        match op_ty_c with
        | none => (unify i qual context ty1 ty2)
        | some ty_c => (
          let context := {context with env_simple := context.env_simple.insert id_bound ty_c}
          (unify i qual context ty1 ty2)
        )

    -------------------------------------

    -- right induction
    | ty', .induc ty =>
      -- NOTE: substitution is necessary to ensure constraint key contains the unsolved variables
      let ty' := (simplify (subst context.env_simple ty'))
      let ty_r := (simplify (subst context.env_simple (.induc ty)))
      if reducible context ty' ty_r then
        unify i qual context ty' (instantiate 0 [Ty.induc ty] ty) 
      else
        match context.env_relational.find? ty' with
        | .some ty_cache => 
          unify i qual context ty_cache (Ty.induc ty)
        | .none => (
          let occurence := (toList (free_vars ty')).any (fun key => occurs context key (.induc ty)) 
          let rlabels := extract_record_labels ty' 
          let is_consistent_variable_record := !rlabels.isEmpty && List.all (toList (extract_record_labels (.induc ty))) (fun l =>
              rlabels.contains l 
            )
          if is_consistent_variable_record && !occurence && wellformed_key ty' then
            let context := {context with 
              env_keychain := index_free_vars context.env_keychain ty' 
              env_relational := context.env_relational.insert ty' (.induc ty),
            }
            (i, [context])
          else 
            (i, []) 
        )

    -- right union
    | ty, .union ty1 ty2 => 
      let (i, contexts_ty1) := (unify i qual context ty ty1)
      let (i, contexts_ty2) := (unify i qual context ty ty2)
      (i, contexts_ty1 ++ contexts_ty2)

    -- left intersection
    | .inter ty1 ty2, ty => 
      let (i, contexts_ty1) := (unify i qual context ty1 ty)
      let (i, contexts_ty2) := (unify i qual context ty2 ty)
      (i, contexts_ty1 ++ contexts_ty2)

    -- top
    | _, .top => (i, [context])

    -- bottom
    | .bot, _ => (i, [context])

    -------------------------------------

    -- unit
    | .unit, .unit => (i, [context])

    -- implication
    | .impli ty_param ty_body, .impli ty_arg ty_res =>

      bind_nl (unify i qual context ty_arg ty_param) (fun i context =>
        (unify i qual context ty_body ty_res)
      ) 

    -- bound variable
    | .bvar id1, .bvar id2  =>
      if id1 = id2 then 
        (i, [context])
      else
        (i, [])

    -- tag
    | .tag l' ty', .tag l ty =>
      if l' = l then
        unify i qual context ty' ty
      else
        (i, [])

    -- field
    | .field l' ty', .field l ty =>
      if l' == l then
        unify i qual context ty' ty
      else
        (i, [])


    | _, _ => (i, []) 

    def stale_boundary (boundary : Nat) : PHashSet Nat :=
      from_list (List.range boundary)

    -- iteritively unify all constraints 
    -- loop through constraints; unify subsequent constraint under contexts generated by previous constraints
    -- ERROR: causes function type inference to break in max example 
    partial def unify_all (i : Nat) (qual : Qual) (contexts : List Context)  : List (Ty × Ty) -> Nat × List Context 
    | [] => (i, contexts)
    | (key, rel) :: constraints =>
      bind_nl (unify_all i qual contexts constraints) (fun i context =>
        unify i qual context key rel
      )

    -- repeatedly call unify_all until fixed point
    -- needed for completeness in case there are dependencies in opposite order of constraint list traversal 
    -- TODO: replace unify_all calls with solve calls
    -- ERROR: diverges
    partial def solve (i : Nat) (qual : Qual) (contexts : List Context) (constraints : List (Ty × Ty)) 
    : Nat × List Context 
    :=
      let (i, contexts') := unify_all i qual contexts constraints
      if contexts' == contexts then
        (i, contexts')
      else
        solve i qual contexts' constraints


    partial def pack (stale : PHashSet Nat) (context : Context) (ty : Ty) :=
      -----------------------
      -- assumption: env_simple is cycle-free  
      -----------------------
      -- TODO: generalize form of constraints to allow a set of mutually dependent subtypings 

      let ty := simplify (subst context.env_simple ty)

      let fids := (free_vars ty)
      if fids.isEmpty then
        ty
      else 

        let constraints : PHashMap Ty Ty := empty

        -- relational constraints
        let constraints : PHashMap Ty Ty := fids.fold (fun constraints fid => 
          if !stale.contains fid then
            match context.env_keychain.find? fid with
            | some keychain =>
              keychain.fold (fun constraints key =>
                (match context.env_relational.find? key with
                | some relation => 
                  let key := subst context.env_simple key
                  if constraints.contains key then
                    constraints
                  else
                    constraints.insert key (pack stale context relation) 
                | none => 
                  -- invariant: this case should never happen
                  constraints 
                )
              ) constraints
            | none => constraints
          else
            constraints
        ) constraints 


        if constraints.isEmpty then
          ty
        else
          intersect_over (fun (ty_lhs, ty_rhs) => 
            let fvs_constraints := (free_vars ty_lhs)
            let fids_c := (toList ((Ty.free_vars ty) +fvs_constraints)).filter (fun id => !stale.contains id)
            [lesstype|
              {⟨abstract fids_c 0 ty⟩ with ⟨abstract fids_c 0 ty_lhs⟩ <: ⟨abstract fids_c 0 ty_rhs⟩ # ⟨fids_c.length⟩}
            ]
          ) constraints.toList

    -- old
    -- partial def pack (boundary : Nat) (context : Context) (ty : Ty) :=
    --   -----------------------
    --   -- assumption: env_simple is cycle-free  
    --   -----------------------

    --   let ty := simplify (subst context.env_simple ty)

    --   let fids := (free_vars ty)
    --   if fids.isEmpty then
    --     ty
    --   else 

    --     let constraints : PHashMap Ty Ty := empty

    --     -- relational constraints
    --     let constraints : PHashMap Ty Ty := fids.fold (fun constraints fid => 
    --       if fid >= boundary then
    --         match context.env_keychain.find? fid with
    --         | some keychain =>
    --           keychain.fold (fun constraints key =>
    --             (match context.env_relational.find? key with
    --             | some relation => 
    --               let key := subst context.env_simple key
    --               if constraints.contains key then
    --                 constraints
    --               else
    --                 constraints.insert key (pack boundary context relation) 
    --             | none => 
    --               -- invariant: this impli should never happen
    --               constraints 
    --             )
    --           ) constraints
    --         | none => constraints
    --       else
    --         constraints
    --     ) constraints 


    --     if constraints.isEmpty then
    --       ty
    --     else
    --       intersect_over (fun (ty_lhs, ty_rhs) => 
    --         let fvs_constraints := (free_vars ty_lhs)
    --         let fids_c := List.filter (fun id => id >= boundary) (toList fvs_constraints)
    --         [lesstype|
    --           {⟨fids_c.length⟩ // ⟨abstract fids_c 0 ty⟩ with ⟨abstract fids_c 0 ty_lhs⟩ <: ⟨abstract fids_c 0 ty_rhs⟩}
    --         ]
    --       ) constraints.toList

-----------------------------------------------------

    -- TODO: remove this; replace with combination of universal generaliztion and packing
    -- deprecated
    /-
    def generalize (boundary : Nat) (context : Context) (ty : Ty) : Ty := (
      -- TODO: figure out way to solve relational constraints to simplify type 
      --------------------------------------
      -- boundary prevents overgeneralizing

      -- sub in simple types; 
      -- subbing prevents strengthening from the outside in 
      -- only the body type (conclusion) can safely strengthen the parameter type (the premise)  
      -- subbing does not prevent weakening, as weakining is handles adding unions of fresh variables  
      --------------------------------------

      -----------------------------
      -- TODO:
      -- rely on pack which does not sub in for parameters
      ---------------------------
        -- let ty_ex := pack boundary context empty ty
        -- [lesstype| ⟨ty_ex⟩ >> β[0]]
      -----------------------
      -----------------------
      let ty := simplify (subst context.env_simple ty)
      let fids_pl := List.filter (fun id => id >= boundary) (toList (free_vars ty))
      -- let constrained := fids_pl.any (fun fid => context.env_keychain.contains fid)  

      if fids_pl.isEmpty then
          ty
      -- else if no_function_types ty then
      --   let env_sub := PHashMap.from_list (
      --     fids.map (fun fid => (fid, Ty.bot))
      --   )
      --   simplify (subst env_sub ty)
      -- else if !constrained then
      --   -- NOTE: need to use universal in order to indicate weakening is allowed for unconstrained variables.
      --   (List.range fids_pl.length).foldl (fun ty_acc _ =>
      --     [lesstype| ? >> ⟨ty_acc⟩]
      --   ) (abstract fids_pl 0 ty)
      else (
        let ty_packed := pack boundary context ty
        let ty_base := [lesstype| ⟨ty_packed⟩ >> β[0]]
        (List.range fids_pl.length).foldl (fun ty_acc _ =>
          [lesstype| ? >> ⟨ty_acc⟩]
        ) (abstract fids_pl 0 ty_base) 
      )
      -----------------------
    )

    -/



    partial def union_all : (List Ty) -> Option Ty
      | [] => none
      | t::ts =>
        let ts := List.filter
          (fun t' => not (t == t'))
          ts
        match union_all ts with
          | .none => .some t
          | .some t' => Ty.union t t'


    def functiontype : Ty -> Bool
    | .field _ _ => true 
    | .inter _ _ => true
    | .impli _ _ => true 
    | .univ _ _ => true
    | _ => false


    partial def unify_reduce_full (i : Nat) 
      (env_simple : PHashMap Nat Ty) (descrip : PHashSet Nat)
      (ty1 ty2 ty_result : Ty) 
    : Option Ty
    :=
      let qual := ⟨descrip⟩
      let context : Context := Context.mk env_simple empty empty 
      let stale : PHashSet Nat := empty 
      let (_, contexts) : Nat × List Context := (unify i qual context ty1 ty2)
      -- let (_, contexts) : Nat × List Context := bind_nl (unify i context ty1 ty2) (fun i context =>
      --   unify_all i [context] context.env_relational.toList
      -- )

      if contexts.isEmpty then
        none
      else
        let intersectable := contexts.all (fun context => 
          functiontype (subst context.env_simple ty_result)
        )

        let intersectable := false

        let result := (
          if intersectable then
            List.foldr (fun context ty_acc => 
              let ty_ex := Ty.pack stale context ty_result
              Ty.intersect [lesstype| [_ <:⟨ty_ex⟩] β[0]] ty_acc
            ) Ty.top contexts 
          else
            List.foldr (fun context ty_acc => 
              let ty_ex := Ty.pack stale context ty_result
              Ty.unionize ty_ex ty_acc
            ) Ty.bot contexts 
        )
        some result

    partial def unify_reduce_env (i : Nat) (env_simple : PHashMap Nat Ty) (ty1) (ty2) (ty_result) :=
      unify_reduce_full i env_simple empty ty1 ty2 ty_result
      
    partial def unify_reduce (i : Nat) (ty1) (ty2) (ty_result) :=
      unify_reduce_full i empty empty ty1 ty2 ty_result

    partial def unify_reduce_adj (adj : PHashSet Nat) (i : Nat) (ty1) (ty2) (ty_result) :=
      unify_reduce_full i empty adj ty1 ty2 ty_result

    partial def unify_simple (i : Nat) (ty1) (ty2) :=
      let qual := ⟨empty⟩
      let context : Context := ⟨empty, empty, empty⟩
      (unify i qual context ty1 ty2)

    partial def unify_envs (i : Nat) (ty1 ty2 : Ty) : List (PHashMap Nat Ty):=
      let qual := ⟨empty⟩
      let context : Context := ⟨empty, empty, empty⟩
      let (i, contexts) := (unify i qual context ty1 ty2)
      contexts.map (fun context => context.env_simple)
      

    partial def unify_decide (i : Nat) (ty1) (ty2) :=
      let qual := ⟨empty⟩
      let context : Context := ⟨empty, empty, empty⟩
      let (_, result) := (unify i qual context ty1 ty2)
      !result.isEmpty

    def combine (icontexts : (Nat × List Context)) (ty : Ty) :=
      let (i, contexts) := icontexts
      (i, contexts.map fun context => (context, ty))

    -- deprecated
    -- def to_pair_type : Ty -> Ty 
    -- | .impli ty1 ty2 => 
    --   [lesstype| ⟨ty1⟩ * ⟨ty2⟩ ] 
    -- | [lesstype| ⊤ ] =>  [lesstype| ⊥ ]
    -- | _ =>  [lesstype| ⊤ ]

    def get_prem : Ty -> Ty 
    | .impli ty1 _ => ty1 
    | .top =>  .bot
    | _ => .top



  end Ty

  inductive Tm : Type
  | hole : Tm 
  | unit : Tm
  | bvar : Nat -> Tm 
  | fvar : Nat -> Tm 
  | tag : String -> Tm -> Tm
  | record : List (String × Tm) -> Tm
  | func : Tm -> Tm
  | matc : Tm -> List (Tm × Tm) -> Tm
  | proj : Tm -> String -> Tm
  | app : Tm -> Tm -> Tm
  | letb : Option Ty -> Tm -> Tm -> Tm
  | fix : Tm -> Tm
  deriving Repr, Inhabited, BEq


  namespace Tm

    declare_syntax_cat lessterm 
    syntax:90 num : lessterm 
    syntax:90 ident : lessterm 
    syntax:90 "(" lessterm ")" : lessterm
    syntax:90 "⟨" term "⟩" : lessterm 
    syntax:90 "_" : lessterm
    syntax:90 ";" : lessterm
    syntax:90 "y[" lessterm:90 "]": lessterm
    syntax:90 "x[" lessterm:90 "]" : lessterm
    syntax:90 "fix" "(" lessterm ")" : lessterm 
    syntax:90 lessterm:90 "(" lessterm ")" : lessterm 

    syntax:80 lessterm:80 "." lessterm:81 : lessterm 
    syntax:80 lessterm:81 ";" lessterm:80 : lessterm

    -- syntax:72 lessterm:73 "|>" lessterm:72 : lessterm 

    syntax:70 lessterm:71 "," lessterm:70 : lessterm

    syntax:60 "if" lessterm:61 "then" lessterm:61 "else" lessterm:60: lessterm

    syntax:60 "@" lessterm:61 "=" lessterm:61 : lessterm
    syntax:60 "@" lessterm:61 "=" lessterm:61 lessterm:60 : lessterm

    syntax:60 "_" "=>" lessterm:60 : lessterm

    syntax:60 "match" lessterm:61 lessterm:50 : lessterm
    syntax:50 "case" lessterm:51 "=>" lessterm : lessterm
    syntax:50 "case" lessterm:51 "=>" lessterm lessterm:50 : lessterm


    syntax:60 "let" "_" ":" lesstype "=" lessterm:60 "in" lessterm:60 : lessterm 
    syntax:60 "let" "_" "=" lessterm:60 "in" lessterm:60 : lessterm 

    syntax:60 "if" lessterm "then" lessterm "else" lessterm : lessterm

    syntax "[lessterm| " lessterm "]" : term

    def record_fields : Tm -> List (String × Tm)
    | record fields => fields
    | _ =>  []

    -- def function_cases : Tm -> List (Tm × Tm)
    -- | func implis => implis 
    -- | _ =>  []

    macro_rules
    | `([lessterm| $n:num ]) => `($n)
    | `([lessterm| $a:ident]) => `($(Lean.quote (toString a.getId)))
    | `([lessterm| _ ]) => `(Tm.hole)
    | `([lessterm| ; ]) => `(Tm.unit)
    | `([lessterm| y[$n] ]) => `(Tm.bvar [lessterm| $n ])
    | `([lessterm| x[$n] ]) => `(Tm.fvar [lessterm| $n ])
    | `([lessterm| fix($a) ]) => `(Tm.fix [lessterm| $a ])
    | `([lessterm| $a($b) ]) => `(Tm.app [lessterm| $a ] [lessterm| $b ])

    | `([lessterm| $a ; $b ]) => `(Tm.tag [lessterm| $a ] [lessterm| $b ])
    | `([lessterm| $a . $b ]) => `(Tm.proj [lessterm| $a ] [lessterm| $b ])
    -- | `([lessterm| $b |> $a ]) => `(Tm.app [lessterm| $a ] [lessterm| $b ])
    | `([lessterm| $a , $b ]) => `(Tm.record [("l", [lessterm| $a ]), ("r", [lessterm|$b ])])

    | `([lessterm| @ $a = $b ]) => `( Tm.record [ ([lessterm| $a ], [lessterm| $b ]) ]  )
    | `([lessterm| @ $a = $b $xs ]) => `( Tm.record (([lessterm| $a ], [lessterm| $b ]) :: (Tm.record_fields [lessterm| $xs ])))

    | `([lessterm| _ => $b ]) => `(Tm.func [lessterm| $b ] )

    | `([lessterm| match $a $b ]) => `(Tm.matc [lessterm| $a ] [lessterm| $b ] )
    | `([lessterm| case $b => $d ]) => `([([lessterm| $b ], [lessterm| $d ])])
    | `([lessterm| case $b => $d $xs ]) => `((([lessterm| $b ], [lessterm| $d ]) :: [lessterm| $xs ]))

    | `([lessterm| let _ : $a = $b in $c ]) => `(Tm.letb (Option.some [lesstype| $a ]) [lessterm| $b ] [lessterm| $c ])
    | `([lessterm| let _ = $b in $c ]) => `(Tm.letb Option.none [lessterm| $b ] [lessterm| $c ])

    | `([lessterm| if $a then $b else $c ]) => `(
        [lessterm| 
          match $a 
          case ⟨Tm.tag "true" Tm.unit⟩ => ($b) 
          case ⟨Tm.tag "false" Tm.unit⟩ => ($c)
        ]
    )

    -- generic
    | `([lessterm| ($a) ]) => `([lessterm| $a ])

    --escape 
    | `([lessterm| ⟨ $e ⟩ ]) => pure e


    #eval [lesstype| [_] β[0] -> {β[0] with β[0] <: β[1] * β[2] }  ]

    #eval [lesstype| [_] β[0] -> {β[0] | unit with β[1] <: β[0] } ]


    -- partial def repr (t : Tm) (n : Nat) : Format :=
    -- match t with
    -- | .hole => 
    --   "_"
    -- | .unit =>
    --   "()"
    -- | .bvar id =>
    --   "y[" ++ (Nat.repr id) ++ "]"
    -- | .fvar id => 
    --   "x[" ++ (Nat.repr id) ++ "]"
    -- | .tag l t1 =>
    --   "#" ++ l ++ " " ++ (repr t1 n)
    -- | record [("l", l), ("r", r)] =>
    --   let _ : ToFormat Tm := ⟨fun t1 => repr t1 n ⟩
    --   Format.bracket "(" (Format.joinSep [l, r] ("," ++ Format.line)) ")"
    -- | record fds =>
    --   let _ : ToFormat (String × Tm) := ⟨fun (l, t1) => "@" ++ l ++ " = " ++ repr t1 n⟩
    --   Format.bracket "(" (Format.joinSep fds (" " ++ Format.line)) ")"
    -- | func fs =>
    --   let _ : ToFormat (Tm × Tm) := ⟨fun (pat, tb) =>
    --     "| " ++ (repr pat n) ++ " => " ++ (repr tb (n))
    --   ⟩
    --   Format.bracket "(" (Format.joinSep fs (" " ++ Format.line)) ")"
    -- | .proj t1 l =>
    --   repr t1 n ++ "/" ++ l
    -- | .app t1 t2 =>
    --   Format.bracket "(" (repr t1 n) ") " ++ "(" ++ repr t2 n ++ ")"
    -- | .letb op_ty1 t1 t2 =>
    --   match op_ty1 with
    --   | some ty1 =>
    --     "let _ : " ++ (Ty.repr ty1 n) ++ " = " ++  (repr t1 n) ++ " in" ++
    --     Format.line  ++ (repr t2 n) 
    --   | none =>
    --     "let _ = " ++  (repr t1 n) ++ " in" ++
    --     Format.line  ++ (repr t2 n) 
    -- | .fix t1 =>
    --   Format.bracket "(" ("fix " ++ (repr t1 n)) ")"

    -- instance : Repr Tm where
    --   reprPrec := repr

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
    | .matc _ _ => none
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
    | .matc arg branches => 
      matc (abstract fids start arg) (List.map (fun (tp, tb) =>
        let n := match pattern_wellformed 0 tp with
        | .some n => n 
        | .none => 0 
        let tp := abstract fids (start + n) tp 
        let tb := abstract fids (start + n) tb
        (tp, tb)
      ) branches)
    | .func body =>
      func (abstract fids (start + 1) body)
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


    partial def instantiate (start : Nat) (subs : List Tm) : Tm -> Tm
    | .hole => hole 
    | .bvar id => 
        if h : start ≤ id ∧ (id - start) < subs.length then
          let i : Fin subs.length := {
            val := (id - start),
            isLt := (match h with | And.intro _ h' => h') 
          } 
          subs.get i 
        else
          .bvar id
    | .fvar id => .fvar id 
    | .unit => .unit 
    | .tag l t => tag l (instantiate start subs t)
    | .record fds =>
      record (List.map (fun (l, t) =>
        (l, instantiate start subs t)
      ) fds)
    | .matc arg branches => 
      matc (instantiate start subs arg) (List.map (fun (tp, tb) =>
        let n := match pattern_wellformed 0 tp with
        | .some n => n 
        | .none => 0 
        let tp := instantiate (start + n) subs tp 
        let tb := instantiate (start + n) subs tb
        (tp, tb)
      ) branches)
    | .func tb =>
      func (instantiate (start + 1) subs tb)
    | .proj t l => 
      proj (instantiate start subs t) l
    | .app t1 t2 =>
      app 
        (instantiate start subs t1) 
        (instantiate start subs t2)
    | .letb ty1 t1 t2 =>
      letb ty1 
        (instantiate start subs t1)
        (instantiate (start + 1) subs t2)
    | .fix t =>
      .fix (instantiate start subs t)



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

    -- def increment (howMuch : Int) : StateM Int Int :=
    --   get >>= fun i =>
    --   set (i + howMuch) >>= fun () =>
    --   pure i

    -- def increment (howMuch : Int) : StateM Int Int := do
    --   let i <- get 
    --   set (i + howMuch) 
    --   pure i

    -- def foo (t : Tm) : StateM Nat (List (Ty × Ty)) := do 
    --   let i <- get
    /-
    - NOTE: use state Monad for fresh variable
    - NOTE: returns type and list of constraints; rather than propagating down expected type
    - constraints formed at application, rather than from downward propagation
    - NOTE: type must be non-empty/inhabited to ensure soundness



    - NOTE: simply return a type; use existential type to include unsolved constraints. 
    -/
    -- def infer (i : Nat) (qual : Ty.Qual) (context : Ty.Context) (env_tm : PHashMap Nat Ty) (t : Tm) : (Nat × List (Ty.Context × Ty)) :=
    partial def to_type_state (env_tm : PHashMap Nat Ty) (t : Tm) : StateT Nat Option Ty :=
    match t with
    | hole =>
      return Ty.top
    | .unit => 
      return Ty.unit
    | bvar _ => 
      failure
    | fvar id => do
      let ty <- env_tm.find? id
      return ty
    | .tag l t1 => do 
      let ty1 <- to_type_state env_tm t1
      return Ty.tag l ty1

    | .record fds => do
      let mut ty_result := Ty.top 
      for (l_i, t_i) in fds.reverse do
        let ty_i <- to_type_state env_tm t_i  
        ty_result := Ty.inter (Ty.field l_i ty_i) ty_result
      return ty_result

    | .matc switch branches => do
      let boundary <- get
      let ty_switch <- to_type_state env_tm switch
      
      let mut ty_result := Ty.bot
      for (p,b) in branches.reverse do
        let n <- pattern_wellformed 0 p
        let env_pat : PHashMap Nat Ty <- modifyGet (fun i => (
          Id.run do
          let mut env_pat : PHashMap Nat Ty := empty 
          for j in (List.range n) do
            let tm_key := (i + (2 * j))
            let ty_x := Ty.fvar (i + (2 * j) + 1) 
            env_pat := (env_pat.insert tm_key ty_x)
          return env_pat
          ,
          i + (2 * n)
        ))

        let list_tm_x := env_pat.toList.map (fun (k, _) => (fvar k))

        let p := instantiate 0 list_tm_x p 
        let b := instantiate 0 list_tm_x b  
        let ty_p <- to_type_state (env_tm ; env_pat) p

        let ty_b <- to_type_state (env_tm ; env_pat) b 
        /-
        NOTE: abstract pattern's type for each case
        -/
        let fids := (toList ((Ty.free_vars ty_b) + (Ty.free_vars ty_p))).filter (fun fid => fid >= boundary)
        let ty_i := Ty.exis (Ty.abstract fids 0 ty_b) [(ty_switch, (Ty.abstract fids 0 ty_p))] fids.length

        ty_result := Ty.union ty_i ty_result
      return ty_result


    | .func body => do
      /-
      abstraction of parameter occurs in let-binding
      -/
      let (env_param, ty_p) <- modifyGet (fun i => (
        let ty_p := Ty.fvar (i + 1)
        (empty.insert i ty_p, ty_p)
        ,
        (i + 2)
      ))

      let list_tm_x := env_param.toList.map (fun (k, _) => (fvar k))

      let b := instantiate 0 list_tm_x body
      let ty_b <- to_type_state (env_tm; env_param) b
      return Ty.impli ty_p ty_b

    | .proj t1 l => do
      let ty1 <- to_type_state env_tm t1
      return Ty.exis (.bvar 0) [(ty1, Ty.field l (.bvar 0))] 1

    | .app t_f t_arg => do
      let ty_arg <- to_type_state env_tm t_arg
      let ty_f <- to_type_state env_tm t_f
      return Ty.exis (.bvar 0) [(ty_f, Ty.impli ty_arg (.bvar 0))] 1 


    | .letb op_ty_expected t_arg t => do

      let ty_expected <- match op_ty_expected with
      | some ty_expected => return ty_expected
      | none => modifyGet (fun i => (Ty.fvar i, i + 1))

      let ty_context <- (do
        if t_arg == Tm.hole then
          return ty_expected
        else
          let ty_arg <- to_type_state env_tm t_arg
          return [lesstype| [_ <: {⟨ty_arg⟩ with ⟨ty_arg⟩ <: ⟨ty_expected⟩ # 0}] β[0] ]
      )

      let (x, env_tmx) <- modifyGet (fun i =>
        ((fvar i, PHashMap.from_list [(i, ty_context)]), i + 1)
      )
      let t := instantiate 0 [x] t 
      to_type_state (env_tm;env_tmx) t

    | .fix t_self_f => do
      let ty_self_f <- to_type_state env_tm t_self_f

      let (id_fixed, ty_IC) <- match ty_self_f with
      | .impli (.fvar id) ty_IC => some (id, ty_IC)
      /-
      TODO: add case for generalized implication: .univ ... 
      -/
      | _ => none 

      return [lesstype| coduct ⟨Ty.abstract [id_fixed] 0 ty_IC⟩ ]
    /-
    END to_type_state
    -/


    def to_type (t : Tm) : Option Ty := do
      let (ty, _) <- to_type_state empty t 0
      let ty := Ty.simplify ty
      /-
      TODO: generalize 
      -/
      -- let fids := toList (Ty.free_vars ty)
      -- let mut ty_univ := (Ty.abstract fids 0 ty)
      -- for _ in fids do
      --   ty_univ := Ty.univ none ty_univ
      return ty

    /-
    TODO: convert type into set of horn clause constraints in for of subtyping
    - e.g. {C & P₁ & P₂ & ... [Y]} <: Q  
    - meaning ∀ X Y . (C[X,Y] & P₁[X,Y] & P₂[X,Y] & ... => Q[X])

    TODO: may need to convert coinductive implication into inductive constraints

    - can think of the type generated from a program as a model
    - although the model may have nested specs due to 
      - body <: annotation in let-binding   
      - arg <: param in application
      - switch <: pattern in matching 
    NOTE: when existential is on rhs
      CORRECT: 
        - induction/existential/union on RHS represents a concrete predicate
        - do no deconstruct
      WRONG:
        - variables should be freed 
        - P <: μ R . nil | {cons X × L with L <: R}
        - P(nil) ==> R(nil)
        - ∀ x,l . P(cons(x,l)) & R(l) ==> R(cons(x,l))
    NOTE: deconstruction of RHS will be handled by craig interpolation during solving
    QUESTION: How is universal on lhs handled? moved to rhs? 
    QUESTION: should universals be converted to existentials? 
    QUESTION: should co-induction be converted to induction? 



    NOTE: generation of horn clauses rewrites types into horn clauses
    -/

    def Clause := List Ty × Ty 

    /-
    TODO: 
    - create a horn clauses syntactic sugar
    - create meta-predicate syntax; meta-predicate is an object-proposition
    - a meta-argument is a proof; proof : proposition
    - predicate is a variable defined by the horn clause
    - use first order predicates and |= for entailment 
    - or use _ |- _ ==> _ for entailment under interpretation  

    TODO:
    - distinguish between rules allowing predicates to be expanded
      - and rules defining constraints; which cannot be expanded
    
    NOTE: comparison of CHC and Prolog 
    - CHC involves the search problem of finding predicates
      - interpolation part is a specialized logic e.g. Prolog/arithmetic
    - Prolog involves the search problem of finding arguments

    NOTE: predicate search
    - C(x) ==> P(x), D(c) ==> P(x) expands P with union P ↦ C | D
    - P(x) ==> C(x) uses craig interpolation to narrow P's dependencies with intersection 

    IDEA: 
    - types with bound variables represent CHC constraints (unadjustable)
    - type variables represent predicates to be learned (adjustable)

    NOTE: the learnable predicate/type for one abstraction becomes the constraint for the outer abstraction 
    NOTE: let annotations, param types, pattern types are constraints
    --------------------------------------
    NOTE: 
    - inductive definitions (used on lhs) can have learnable predicates
    - Thus it is safe to convert an observed inductive type into horn clause constraints over a type variable.
    - types on RHS, (e.g. annotations, param/pattern types) are not converted into horn clauses!
    - types on RHS are constraints and are not learnable
    - is that enough? is any else necessary to mark learnable type variables?
    - all free variables are learnable
    - free variables that represent parameter will be constrained by types/predicates originating at pattern matching
    - the outer horn clause language is for coarsely learning predicates
    - the inner constraint sublanguage is for refining the predicates
      - the inner language may be Prolog-like
    - the constraint (RHS) is searched by introducing a new learnable predicate that implies RHS constraint
      - e.g. P(x, y), y = label ==> C(x, y)
      - e.g. P & {x,y | y = label} ==> C(x, y)
      - i.e. a constraint is made learnable by introducing a new learnable variable under a constraint
      - solving for the concrete value of X requires a specialized logic that understands the full type language
        - including the labels (tags, fields), implication, quantifiers, induction, etc.
    ------------------------------------------------
    -/
    def to_CHC : Ty -> StateT Nat Option ((List Clause) × Ty)
    | .tag l ty_pl => do
      let (clauses_pl, head_pl) <- to_CHC ty_pl  
      -- ALTERNATIVE: use propositions and fresh ID in head position
      -- return (([.tag l head_pl], ID) :: clauses_pl, ID)
      -- return (([head_pl(h)] ==> ID(.tag l h)) :: clauses_pl, ID)
      return (([], .tag l head_pl) :: clauses_pl, .tag l head_pl)
    /- --| TODO |-- -/
    | _ => failure 
    -- def to_clauses : Ty -> Option ((List Clause) × Ty)
    -- | .bvar _ => failure  
    -- | .fvar id => return ([([], .fvar id)], .fvar id) 
    -- | .unit => return ([([], .unit)], .unit) 
    -- | .top => return ([([], .top)], .top)
    -- | .bot => return ([([], .bot)], .bot)
    -- | .tag l ty_pl => do
    --   let (clauses_pl, head_pl) <- to_clauses ty_pl  
    --   -- ALTERNATIVE: use propositions and fresh ID in head position
    --   -- return (([.tag l head_pl], ID) :: clauses_pl, ID)
    --   -- return (([head_pl(h)] ==> ID(.tag l h)) :: clauses_pl, ID)
    --   return (([], .tag l head_pl) :: clauses_pl, .tag l head_pl)
    -- /- --| TODO |-- -/
    -- | _ => failure 
    -- | .field : String -> Ty -> Ty
    -- | .union : Ty -> Ty -> Ty
    -- | .inter : Ty -> Ty -> Ty
    -- | .impli : Ty -> Ty -> Ty
    -- /- payload -> List (lower <: upper) -> bound -> Ty -/
    -- | .exis : Ty -> List (Ty × Ty) -> Nat -> Ty
    -- -- TODO: remove Option from univ; top type is sufficient
    -- | .univ : Option Ty -> Ty -> Ty
    -- | .induc : Ty -> Ty
    -- | .coduc : Ty -> Ty

    -----------------------

    /-
    - NOTE: constraint on parameter via body's existential seems sound 
    - this implies that a type such as (P -> bot) can be constructed
    - logically this means ¬ P, which seems ok.
    - therefore constraint in universal is not actually necessary over implication
    - it is subsumed by constraint in existential
    - however, if body of universal is not an implication then universal constraint is helpful
    -/

    def nat_to_chain := [lessterm|
      fix(_ => _ => match y[0] 
      case zero;; => nil;;
      case succ;y[0] => cons;(y[2](y[0]))
      )
    ] 
    /-
    Expected:
    (coduct (α[3] ->
      {cons//{β[0] with β[2] <: (β[1] -> β[0]) # 1} with α[3] <: succ//β[0] # 1} |
      {nil//unit with α[3] <: zero//unit # 0} | 
      bot
    ))
    -/
    #eval to_type nat_to_chain

    ------------------
    def nat_to_list := [lessterm|
      (_ => fix(_ => _ => match y[0] 
        case zero;; => nil;;
        case succ;y[0] => cons;(y[3], y[2](y[0]))
      ))
    ]
    /-
    Expected:
    (α[1] -> (coduct (α[5] ->
      {nil//unit with α[5] <: zero//unit # 0} |
      {cons//(α[1] * {β[0] with β[2] <: (β[1] -> β[0]) # 1}) with α[5] <: succ//β[0] # 1}
    )))
    -/
    #eval to_type nat_to_list

    ------------------

    def le := [lessterm| 
      fix (_ => _ => match y[0]
        case (zero;;, y[0]) => true;;  
        case (succ; y[0], succ; y[1]) => (y[3] (y[0], y[1])) 
        case (succ; y[0], zero;;) => false;; 
      )
    ]

    #eval to_type le 

    def max := [lessterm| 
      let _ = ⟨le⟩ in
      (_ => match y[0] case (y[0], y[1]) =>
        (
          if (y[3] (y[0], y[1])) then
            y[1]
          else
            y[0]
        )
      )
    ] 

    #eval to_type max

    def lt := [lessterm|
      fix (_ => _ => match y[0]
        case (zero;;, succ;zero;;) => true;;  
        case (succ; y[0], succ; y[1]) => (y[3] (y[0], y[1])) 
        case (y[0], zero;;) => false;; 
      )
    ]

    def add := [lessterm|
      fix(_ => _ => match y[0] 
        case (zero;;, y[0]) => y[0] 
        case (succ; y[0], y[1]) => succ; (y[3] (y[0], y[1]))
      )
    ]

    #eval to_type add 

    def sum := [lessterm|
      fix(_ => _ => match y[0]
        case zero;; => zero;; 
        case succ; y[0] => (
          (⟨add⟩)((y[2](y[0]), succ;y[0]))
        )
      )
    ]

    #eval to_type sum 

    def foldn := [lessterm|
      let _ = _ in
      let _ = _ in
      _ => match y[0] case (y[0], (y[1], y[2])) => (
          let _ = fix(_ => _ => match y[0] case (y[0], y[1]) =>
            /-
            n, b, f: 4, 5, 6 
            loop: 3 
            i, c: 0, 1 
            -/
            (if ⟨lt⟩(y[0], y[4]) then
              -- y[3](succ;y[0], y[6](y[0], y[1]))
              y[3](succ;y[0], ;)
            else
              y[1]
            )
          ) in 
          /-
          loop: 0 
          n: 1
          b: 2
          f: 3
          -/
          y[0](zero;;, y[2])
          -- y[0]
      )
    ]

    #eval to_type foldn 

    -----------------------
    -----------------------
    -----------------------

      -- match ty_self_f with
      -- | .impli ty_IH ty_IC =>
      /-
      - inductive_branches --rename--> ty_self_f
      - ty_self_f should 

        induct nat_list
          (zero × nil) 
          {succ n × cons l with n × l <: nat_list}

        --------
        - step 0: SELF -> X -> {nil with X <: zero} | {cons L with X <: succ N, SELF <: N -> L [N, L]}
        - this is co-inductive: want the GREATEST fixed point, which is the least number of conjunctions (intersections)
        - coducuct SELF . X -> {nil with X <: zero} | {cons L with X <: succ N, SELF <: N -> L [N, L]}
        - translate to LEAST fixed point of body; which is the least number of disjunctions (unions):
        - step 1: REL = induct SELF . {zero * nil} | {succ N * cons L with N * L <: SELF [N, L]}
        - step 2: F = {X -> Y with X * Y <: REL}
        - step 3: [T<:F] T 
        - TODO: verify that translation is logically valid according to duality
        - if it is valid; generate the simpler co-inductive type; then translate it to constraints for CHC solver
        - if it's not valid; construct an inductive type
        ----
        -- NOTE: when converting co-inductive type into constraints; remove quantifiers and and place inductive binding in premise 
        -- i.e. coducuct X . T  becomes X <: T
        ----
        SELF -> X -> {nil with X <: zero} | {cons L with X <: succ N, SELF <: N -> L [N, L]}
        coduc SELF . X -> {nil with X <: zero} | {cons L with X <: succ N, SELF <: N -> L [N, L]}
        --- assuming constraints on X are disjoint --- this is probably an unnecssary step that would strengthen in if not disjoint
        coduc SELF . X -> {nil with X <: zero} & X -> {cons L with X <: succ N, SELF <: N -> L [N, L]}
        coduc SELF . zero -> nil & {succ N -> cons L SELF <: N -> L [N, L]}
        ¬ induct SELF . zero × ¬ nil | {succ N × ¬ cons L with N × ¬L <: SELF [N, L]})
        induct SELF . zero × ¬ nil | {succ N × ¬ cons L with N × ¬L <: SELF [N, L]} -> F
        {X × ¬ Y -> F with X * Y <: REL} ; REL = induct SELF . zero × nil | {succ N × cons L with N × L <: SELF [N, L]}
        {X -> Y with X * Y <: REL}
      -/
      -------------
      -------------
      -- let ty_content := inductive_branches.foldr (fun (context, ty_branch) ty_acc =>
      --   match ty_branch with
      --   | .impli ty_IH ty_IC => 
      --     let ty_IH := Ty.subst context.env_simple ty_IH
      --     let ty_IC := Ty.subst context.env_simple ty_IC

      --     match ty_IH, ty_IC with
      --     | .impli ty_IH_ante ty_IH_consq, .impli ty_IC_ante ty_IC_consq => (
      --       /-
      --       abstract/pack type of application in tail position 
      --       -/
      --       let stale_consq := (Ty.stale_boundary boundary) + (Ty.free_vars ty_IH_consq)
      --       let ty_IC_consq := Ty.pack stale_consq context ty_IC_consq
      --       let ty_IC_pair := [lesstype| ⟨ty_IC_ante⟩ * ⟨ty_IC_consq⟩]

      --       let ty_IH_pair := [lesstype| ⟨ty_IH_ante⟩ * ⟨ty_IH_consq⟩]

      --       let fvs_IH := Ty.free_vars ty_IH_pair
      --       let fvs_IC := Ty.free_vars ty_IC_pair
      --       let fvs := (toList (fvs_IH + fvs_IC)).filter (fun fid => fid >= boundary)
      --       let ty_choice := (
      --         if !(fvs_IH * fvs_IC).isEmpty then
      --           let fixed_point := fvs.length
      --           [lesstype|
      --             {⟨Ty.abstract fvs 0 ty_IC_pair⟩ with 
      --               ⟨Ty.abstract fvs 0 ty_IH_pair⟩ <: β[⟨fixed_point⟩] 
      --               #
      --               ⟨fvs.length⟩
      --             } 
      --           ]
      --         else if fvs.length > 0 then
      --           [lesstype| {⟨Ty.abstract fvs 0 ty_IC_pair⟩ # ⟨fvs.length⟩} ]
      --         else
      --           ty_IC_pair
      --       )

      --       /-
      --       include other constraints on variables with along with inductive constraint
      --       -/
      --       -- let ty_IC_packed := Ty.pack (Ty.stale_boundary boundary) context ty_IC_pair
      --       -- let ty_choice := (
      --       --   if ty_IC_packed == Ty.simplify (Ty.subst context.env_simple ty_IC_pair) then
      --       --     ty_choice
      --       --   else 
      --       --     Ty.intersect ty_choice ty_IC_packed
      --       -- )

      --       (Ty.union ty_choice ty_acc) 
      --     )
      --     | .fvar id_IH, .impli ty_IC_ante ty_IC_consq => (
      --       let stale_consq := (Ty.stale_boundary boundary)
      --       let ty_IC_consq := Ty.pack stale_consq context ty_IC_consq
      --       let ty_IC_pair := [lesstype| ⟨ty_IC_ante⟩ * ⟨ty_IC_consq⟩]

      --       let fvs := (toList (Ty.free_vars ty_IC_pair)).filter (fun fid => fid >= boundary)
      --       let ty_choice := (
      --         if fvs.length > 0 then
      --           [lesstype| {⟨Ty.abstract fvs 0 ty_IC_pair⟩ # ⟨fvs.length⟩} ]
      --         else
      --           ty_IC_pair
      --       )
      --       (Ty.union ty_choice ty_acc) 
      --     )
      --     | _, _ => Ty.top
      --   | _ => (Ty.tag "other" Ty.unit)
      -- ) Ty.bot

      -- let ty_rel := [lesstype| induct ⟨ty_content⟩ ]
      -- let ty' := Ty.simplify [lesstype| [_<:{β[1] -> β[0] with β[1] * β[0] <: ⟨ty_rel⟩ # 2}] β[0]] 


      -- -- let context := {context with env_simple := context.env_simple.insert 666 (Ty.tag s!"msg_{i}_" Ty.unit)}
      -- let context := {context with env_simple := context.env_simple.insert 666 (Ty.tag s!"boundary_{boundary}_" Ty.unit)}

      -- (i, [(context, ty')])
      ----------------------
      ----------------------

    --------------
    /-


      ------------------

      ---------
      -- bind_nl (infer i qual context env_tm t1) (fun i (context, ty1) =>
      -- let (i, tvar_IH) := (i + 1, i) 
      -- let context := {context with env_simple := context.env_simple.insert 666 (Ty.tag s!"IH_{tvar_IH}" Ty.unit)}
      -- let (i, tvar_IC) := (i + 1, i) 
      -- bind_nl (Ty.unify i qual context ty1 (Ty.impli (Ty.fvar tvar_IH) (Ty.fvar tvar_IC))) (fun i context =>
      -- let ty_IH := Ty.simplify (Ty.subst context.env_simple (Ty.fvar tvar_IH))
      -- match ty_IH with
      -- | .impli ty_IH1 ty_IH2 => (
      --   let ty_IC := Ty.subst context.env_simple (Ty.fvar tvar_IC)
      --   let ty_IH_pair := [lesstype| ⟨ty_IH1⟩ * ⟨ty_IH2⟩]
      --   let ty_content := List.foldr (fun ty_impli ty_acc =>
      --     match ty_impli with
      --     | .impli ty_ante ty_consq => (
      --       let vars_IH2 := Ty.free_vars ty_IH2 
      --       let stale_consq := (Ty.stale_boundary boundary) + vars_IH2

      --       -- associate the return type with other types it's related to (including inductive references)
      --       let ty_consq := Ty.pack stale_consq context ty_consq
      --       let ty_payload := [lesstype| ⟨ty_ante⟩ * ⟨ty_consq⟩]

      --       let fvs := (toList (Ty.free_vars ty_payload)).filter (fun fid => fid >= boundary)
      --       let fvs_prem := (Ty.free_vars ty_IH_pair)
      --       let ty_choice := (
      --         if List.any fvs (fun id => fvs_prem.find? id != none) then
      --           let fixed_point := fvs.length
      --           [lesstype|
      --             {⟨fvs.length⟩ # ⟨Ty.abstract fvs 0 ty_payload⟩ with 
      --               ⟨Ty.abstract fvs 0 ty_IH_pair⟩ <: β[⟨fixed_point⟩] 
      --             } 
      --           ]
      --         else if fvs.length > 0 then
      --           [lesstype| {⟨fvs.length⟩ # ⟨Ty.abstract fvs 0 ty_payload⟩} ]
      --         else
      --           ty_payload
      --       )

      --       (Ty.union ty_choice ty_acc) 
      --     )
      --     | _ => Ty.top

      --   ) .bot (Ty.split_intersections ty_IC)

      --   /-
      --   NOTE: constraint that ty' <= ty_IH is built into inductive type
      --   -/
      --   -- let relational_type := [lesstype| induct ⟨ty_content⟩ ]
      --   -- let ty' := Ty.simplify [lesstype| [_<:{2 # β[1] -> β[0] with β[1] * β[0] <: ⟨relational_type⟩}] β[0]] 
      --   -- (i, [(context, ty')])

      -- )
      -- | _ => 
      --   (i, [])
      -- ))


      -- debugging --
      -- bind_nl (infer i context env_tm t1) (fun i (context, ty1) =>
      -- bind_nl (Ty.unify i context ty1 (Ty.impli (Ty.fvar tvar_IH) (Ty.fvar tvar_IC))) (fun i context =>
      --   (i, [(context, ty1)])
      -- ))
      ---------------

      -- bind_nl (Ty.unify i context (ty_IH) (Ty.impli (Ty.fvar tvar_IH1) (Ty.fvar tvar_IH2))) (fun i context =>
      ------
      -- let ((i, contexts), ty_IH1, ty_IH2) := (match ty_IH with
      --   | .impli ty_IH1 ty_IH2 => ((i, [context]), ty_IH1, ty_IH2)
      --   | _ => 
      --     let (i, ty_IH1) := (i + 1, Ty.fvar i) 
      --     let (i, ty_IH2) := (i + 1, Ty.fvar i) 
      --     (Ty.unify i context ty_IH (Ty.impli ty_IH1 ty_IH2), ty_IH1, ty_IH2)
      -- )
      -- bind_nl (i, contexts) (fun i context =>


      -- (i, [(context, ty_IH)])

      -- let debug_msg := (
      --   match ty_IH with
      --   | Ty.fvar id => if context.env_simple.contains id then s!"assigned_{id}" else s!"UNassigned_{id}"
      --   | _ => "non-var"
      -- )

      ----------
      -- let ty_fresh := Ty.fvar 666
      -- let context := {context with env_simple := context.env_simple.insert 666 ty_IH}
      -- let context := {context with env_simple := context.env_simple.insert 777 (Ty.tag debug_msg Ty.unit)}
      -- (i, [(context, ty_fresh)])
      ----
      -- OBSERVATION: the ty_IH is a variable and is not yet assigned to an implication; be eventually will be  
      -- CHALLENGE: how to add a requirement to this variable such that future assignments can be decomposed into inductive case?
      -- IDEA: create assignment to fresh variables: X -> Y; construct relational type using fresh variables; 
      -- future applications will then unify with fresh variables
      --------------
      -- (i, [(context, Ty.bot)])
      -- (i, [(context, ty_IH)])
      -- TODO: why does ty_IH allow the type inference in the other case to pass, but the others don't?
      -- probably related to application's requirement that all argument types pass
      -- (i, [])
      -- (i, [(context, Ty.tag "booga_ty_IH" ty_IH)])
      -- (i, [(context, Ty.top)])

    -/

    -- partial def infer_simple i (t : Tm) :=
    --   let qual := ⟨empty⟩
    --   let context : Ty.Context := ⟨empty, empty, empty⟩
    --   (infer (i + 1) qual context {} t)

    -- partial def infer_envs (i : Nat) (t : Tm) : List (PHashMap Nat Ty) :=
    --   let qual := ⟨empty⟩
    --   let context : Ty.Context := ⟨empty, empty, empty⟩
    --   let (i, context_tys) := (infer (i + 1) qual context {} t)
    --   context_tys.map (fun (context, ty) => context.env_simple)

    -- partial def infer_reduce_context (i : Nat) (qual : Ty.Qual) (context : Ty.Context) (t : Tm) : Option Ty :=
    --   let boundary := 0
    --   let (_, context_tys) := (infer i qual context {} t) 
    --   -- let (_, context_tys) := bind_nl (infer i context {} t) (fun i (context, ty) =>
    --   --   bind_nl (Ty.unify_all i [context] context.env_relational.toList) (fun i context =>
    --   --     (i, [(context, ty)])
    --   -- ))

    --   if context_tys.isEmpty then
    --     none
    --   else
    --     let intersectable := context_tys.all (fun (context, ty_result) => 
    --       Ty.functiontype (Ty.subst context.env_simple ty_result)
    --     )
    --     let intersectable := false

    --     let ty_collapsed := (
    --       if intersectable then
    --         List.foldr (fun (context, ty') ty_acc => 
    --           let ty_ex := Ty.pack (Ty.stale_boundary boundary) context ty' 
    --           Ty.intersect [lesstype| [_ <: ⟨ty_ex⟩] β[0]] ty_acc
    --         ) Ty.top context_tys 
    --       else
    --         List.foldr (fun (context, ty') ty_acc => 
    --           let ty_ex := Ty.pack (Ty.stale_boundary boundary) context ty'
    --           Ty.unionize ty_ex ty_acc
    --         ) Ty.bot context_tys
    --     )
    --     some ty_collapsed


    -- partial def infer_reduce (i : Nat) (t : Tm) : Option Ty := 
    --   let qual := ⟨empty⟩
    --   let context : Ty.Context := ⟨empty, empty, empty⟩
    --   infer_reduce_context (i + 1) qual context t

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
    -- | func implis =>
    --   List.foldl (fun cost' (p, t_b) => cost' + (cost t_b)) 1 implis
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
    -- | func implis =>
    --   let implis' := List.map (fun (p, t_b) => 
    --     (p, subst m t_b)
    --   ) implis 
    --   func implis'
    -- | proj t l => proj (subst m t) l
    -- | app t1 t2 => app (subst m t1) (subst m t2)
    -- | letb ty t1 t2 => letb ty (subst m t1) (subst m t2)
    -- | .fix t => .fix (subst m t)

    -- -- (tag labels, field labels)
    -- partial def extract_labels : Ty -> (List String × List String)
    -- | .bvar id => ([], []) 
    -- | .fvar id => ([], [])
    -- | .unit => ([], []) 
    -- | .top => ([], [])
    -- | .bot => ([], [])
    -- | .tag l ty => 
    --   let (ls_t, ls_f) := extract_labels ty
    --   (l :: ls_t, ls_f) 
    -- | .field l ty => 
    --   let (ls_t, ls_f) := extract_labels ty
    --   (ls_t, l :: ls_f) 
    -- | .union ty1 ty2 => 
    --   let (ls_t1, ls_f1) := extract_labels ty1
    --   let (ls_t2, ls_f2) := extract_labels ty2
    --   (ls_t1 ++ ls_t2, ls_f1 ++ ls_f2) 
    -- | .inter ty1 ty2 => 
    --   let (ls_t1, ls_f1) := extract_labels ty1
    --   let (ls_t2, ls_f2) := extract_labels ty2
    --   (ls_t1 ++ ls_t2, ls_f1 ++ ls_f2) 
    -- | .impli ty1 ty2 => 
    --   let (ls_t1, ls_f1) := extract_labels ty1
    --   let (ls_t2, ls_f2) := extract_labels ty2
    --   (ls_t1 ++ ls_t2, ls_f1 ++ ls_f2) 
    -- | .exis n ty_c1 ty_c2 ty =>
    --   let (ls_tc1, ls_fc1) := extract_labels ty_c1
    --   let (ls_tc2, ls_fc2) := extract_labels ty_c2
    --   let (ls_t, ls_f) := extract_labels ty
    --   (ls_tc1 ++ ls_tc2 ++ ls_t, ls_fc1 ++ ls_fc2 ++ ls_f) 
    -- | .univ op_ty_c ty =>
    --   let (ls_tc, ls_fc) := (match op_ty_c with
    --   | none => ([], [])
    --   | some ty_c => extract_labels ty_c
    --   )
    --   let (ls_t, ls_f) := extract_labels ty
    --   (ls_tc ++ ls_t, ls_fc ++ ls_f) 
    -- | .induc ty =>
    --   extract_labels ty


    -- partial def enumerate_fields : List String -> List (List (String × Tm))
    -- | [] => []
    -- | l :: ls =>
    --   (enumerate_fields ls).map (fun fields => (l, hole) :: fields)

    -- partial def enumerate_implis : List String -> List (List (Tm × Tm))
    -- | [] => []
    -- | l :: ls =>
    --   (enumerate_implis ls).map (fun implis => ([lessterm| ⟨l⟩;y[0] ], [lessterm| _ ]) :: implis)

    -- partial def join_functions (t1 : Tm) (t2 : Tm) : List Tm := match t1, t2 with
    -- | func implis1, func implis2 => [func (implis1 ++ implis2)]
    -- | _, _ => []

    -- partial def enumerate (i : Nat) (env_tm : PHashMap Nat Ty) (ty : Ty) : List Tm :=
    --   let (ls_t, ls_f) := (extract_labels ty)
    --   let tags := ls_t.map (fun l => tag l hole)

    --   let fields := enumerate_fields ls_f
    --   let records := fields.map (fun fds => record fds)

    --   let implis := enumerate_implis ls_t
    --   let functions := (
    --     [lessterm| \ y[0] => _ ] :: 
    --     (implis.map (fun implis => func implis))
    --   )

    --   [lessterm| () ] ::
    --   tags ++
    --   records ++
    --   functions ++
    --   [ [lessterm| let _ = _ in _ ] ] ++
    --   [ [lessterm| fix(_)] ] ++
    --   List.bind env_tm.toList (fun (x, ty) =>
    --     let (_, ls) := extract_labels ty
    --     let var := (fvar x)
    --     let application := [lessterm| let _ = ⟨fvar x⟩(_) in _ ] 
    --     let projections := ls.map (fun l =>
    --       [lessterm| let _ = (⟨fvar x⟩.⟨l⟩) in _ ] 
    --     )
    --     var :: application :: projections
    --   )

  end Tm



--------------------------------------------------
  -- open Ty Tm

  --- unification --
--   def nat_ := [lesstype|
--     induct 
--       zero//unit |
--       succ//β[0]
--   ]

  
    
--   #eval unify_decide 30
--   [lesstype| (zero//unit) ] 
--   [lesstype| zero//unit | succ//unit ]


--   #eval unify_reduce 30
--   [lesstype| (succ//succ//succ//α[0]) ] 
--   [lesstype| zero//unit | succ//⟨nat_⟩ ] 
--   [lesstype| α[0] ]

--   #eval unify_decide 30
--   [lesstype| (succ//succ//succ//zero//unit) ] 
--   [lesstype| zero//unit | succ//⟨nat_⟩ ]

--   #eval unify_reduce 30
--   [lesstype| (succ//α[0]) ] 
--   nat_
--   [lesstype| α[0] ]

--   def nat_list := [lesstype| 
--     induct 
--       (zero//unit * nil//unit) | 
--       {succ//β[0] * cons//β[1] with (β[0] * β[1]) <: β[2]}
--   ]

--   #eval unify_reduce 30
--   [lesstype| (succ//zero//unit) * cons//α[0] ] 
--   nat_list
--   [lesstype| α[0] ]

--   #eval unify_reduce 30
--   [lesstype| succ//zero//unit * α[0] ]
--   [lesstype| ⟨nat_list⟩ ]
--   [lesstype| α[0] ]

--   -- subtyping via local constraints
--   -- expected: nil//unit
--   #eval unify_reduce 30
--   [lesstype| {β[0] with succ//zero//unit * β[0] <: ⟨nat_list⟩} ]
--   [lesstype| cons//α[0] ] 
--   [lesstype| α[0] ]


--   -- expected: cons//nil//unit
--   #eval unify_reduce 30
--   [lesstype| [_<:top] β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} ]
--   [lesstype| succ//succ//zero//unit -> cons//α[0] ] 
--   [lesstype| α[0] ]


--   -----------------------------------------------

--   def even_list := [lesstype| 
--     induct 
--       (zero//unit * nil//unit) | 
--       {succ//succ//β[0] * cons//cons//β[1] with (β[0] * β[1]) <: β[2]}
--   ]


--   -- affected by direction of variable assigment
--   -- expected: true
--   #eval unify_decide 0 even_list nat_list 

--   -- expected: false 
--   #eval unify_decide 0 nat_list even_list

--   def even := [lesstype| 
--     induct zero//unit | succ//succ//β[0]
--   ]

--   ---------------------------------
--   #eval unify_decide 0 even nat_ 
--   #eval unify_decide 0 nat_ even
--   ------------------------

--   -- expected: true
--   #eval unify_decide 0
--   [lesstype| [_] β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} ]
--   [lesstype| [_] β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} ]


--   -- expected: cons//nil//unit
--   #eval unify_reduce 10
--   [lesstype| [_<:{β[0] -> β[1] with β[0] * β[1] <: ⟨nat_list⟩ # 2}] β[0]]
--   [lesstype| succ//zero//unit -> α[2]]
--   [lesstype| α[2]]


--   -- expected: cons//nil//unit
--   #eval unify_reduce 10
--   [lesstype| succ//zero//unit -> α[2]]
--   [lesstype| {β[0] -> β[1] with β[0] * β[1] <: ⟨nat_list⟩ # 2}]
--   [lesstype| α[2]]

--   ----------------

--   -- expected: none 
--   #eval unify_reduce 10
--   [lesstype| {β[0] -> β[1] with β[0] * β[1] <: ⟨nat_list⟩ # 2}]
--   [lesstype| succ//zero//unit -> α[2]]
--   [lesstype| α[2]]

--   -- expected: cons//nil//unit 
--   #eval unify_reduce 10
--   [lesstype| succ//zero//unit -> α[2]]
--   [lesstype| {β[0] -> β[1] with β[0] * β[1] <: ⟨nat_list⟩ # 2}]
--   [lesstype| α[2]]


--   -- potential CYCLE avoided by equality check before substitution
--   -- substitution could cause the same unification problem to repeat infinitely
--   -- expected: true
--   #eval unify_decide 10 
--   [lesstype| [_<:α[0]] β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} ]
--   [lesstype| [_<:α[0]] β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} ]

--   -- expected: true
--   #eval unify_decide 10 
--   [lesstype| α[1] -> {β[0] with α[1] * β[0] <: ⟨nat_list⟩} ]
--   [lesstype| α[2] -> {β[0] with α[2] * β[0] <: ⟨nat_list⟩} ]

--   #eval unify_simple 10 
--   [lesstype| α[1] -> α[3] ]
--   [lesstype| α[2] -> α[4] ]

--   -- expected: true 
--   #eval unify_decide 10 
--   [lesstype| {β[0] with α[1] * β[0] <: ⟨nat_list⟩} ]
--   [lesstype| {β[0] with α[1] * β[0] <: ⟨nat_list⟩} ]

--   -- expected: false 
--   #eval unify_decide 10 
--   [lesstype| {β[0] with α[1] * β[0] <: ⟨nat_list⟩} ]
--   [lesstype| {β[0] with α[2] * β[0] <: ⟨nat_list⟩} ]

--   -- expected: true
--   #eval unify_decide 10 
--   [lesstype| {α[1] * β[0] with α[1] * β[0] <: ⟨nat_list⟩} ]
--   [lesstype| {α[2] * β[0] with α[2] * β[0] <: ⟨nat_list⟩} ]

--   -- expected: true
--   #eval unify_decide 10 
--   [lesstype| {β[0] * β[1] with β[0] * β[1] <: ⟨nat_list⟩} ]
--   [lesstype| {β[0] * β[1] with β[0] * β[1] <: ⟨nat_list⟩} ]

--   -- expected: true
--   #eval unify_decide 10 
--   [lesstype| {β[0] with β[0] <: ⟨nat_list⟩} ]
--   [lesstype| {β[0] with β[0] <: ⟨nat_list⟩} ]

--   -- expected: true
--   #eval unify_decide 10 
--   [lesstype| ⟨nat_list⟩ ]
--   [lesstype| ⟨nat_list⟩ ]
-- ---------------

--   def plus := [lesstype| 
--     induct 
--       {x : zero//unit & y : β[0] & z : β[0]} | 
--       {x : succ//β[0] & y : β[1] & z : succ//β[2] with (x : β[0] & y : β[1] & z : β[2]) <: β[3] }
--   ]

--   #eval plus

--   #eval unify_reduce 30 [lesstype|
--     (
--       x : (α[10]) &
--       y : (succ//zero//unit) & 
--       z : (succ//succ//zero//unit)
--     )
--   ] plus
--   [lesstype| α[10] ]

--   #eval unify_reduce 30 
--     [lesstype|
--       (
--         x : (zero//unit) &
--         y : (zero//unit) & 
--         z : (zero//unit)
--       )
--     ] 
--     plus
--     [lesstype| unit ]

--   #eval unify_reduce 30 
--     [lesstype|
--       (
--         x : (succ//zero//unit) &
--         y : (succ//succ//zero//unit) & 
--         z : (succ//succ//succ//zero//unit)
--       )
--     ] 
--     plus
--     [lesstype| unit ]


--   #eval unify_reduce 30 [lesstype|
--     (
--       x : (succ//zero//unit) & 
--       y : (α[10]) &
--       z : (succ//succ//succ//zero//unit)
--     )
--   ] plus
--   [lesstype| α[10] ]


--   #eval unify_reduce 30 [lesstype|
--     (
--       x : succ//α[1] &
--       y : α[2] &
--       z : (succ//succ//zero//unit)
--     )
--   ] plus
--   [lesstype| α[1] * α[2] ]



--   -- expected: none 
--   #eval unify_reduce 30 
--   [lesstype| (α[0] * zero//unit) | (zero//unit * α[0]) ] 
--   [lesstype| (⟨nat_⟩ * zero//unit) ] 
--   [lesstype| α[0] ]



--   #eval unify_reduce 30 [lesstype|
--     (
--       x : succ//α[0] &
--       y : α[2] &
--       z : (succ//succ//zero//unit)
--     )
--   ] plus
--   [lesstype| succ//α[0] * α[2] ]

--   #eval unify_reduce 30 [lesstype|
--     (
--       x : α[0] &
--       y : α[2] &
--       z : (succ//succ//zero//unit)
--     )
--   ] plus
--   [lesstype| α[0] * α[2] ]

--   #eval unify_reduce 1 [lesstype|
--     (
--       x : (succ//succ//zero//unit) & 
--       y : (succ//zero//unit) &
--       z : (α[0])
--     )
--   ] plus
--   [lesstype| α[0] ]
--   -- == [lesstype| succ//succ//succ//zero//unit ]

--   #eval unify_reduce 30 [lesstype|
--     (
--       x : (succ//zero//unit) & 
--       y : (α[10]) &
--       z : (succ//succ//zero//unit)
--     )
--   ] plus
--   [lesstype| α[10] ]


--   #eval unify_reduce 10 [lesstype|
--   (
--     x : α[5] &
--     y : succ//zero//unit &
--     z : succ//succ//zero//unit
--   )
--   ] plus
--   [lesstype| α[5] ]

--   #eval unify_simple 10 
--     .bot
--     plus 

--   #eval unify_simple 10 
--     plus 
--     .bot

--   ------ type inference --------
--   #eval infer_reduce 0 [lessterm|
--     succ;zero;;
--   ]


--   -- path discrimination

--   -- expected: cons//nil//unit
--   #eval infer_reduce 0 [lessterm|
--     let _ : (zero//unit -> nil//unit) & (succ//zero//unit -> cons//nil//unit) = _ in 
--     (y[0] (succ;zero;;))
--   ]

--   #eval infer_reduce 10 
--   [lessterm|
--   let _ : (
--     ([_] (hello//β[0] -> world//unit)) & 
--     ([_] one//β[0] -> two//unit)
--   ) = _ in 
--   y[0](one;;)
--   ]

--   #eval infer_reduce 10 
--   [lessterm|
--   let _ : (
--     ([_] 
--       (hello//β[0] -> world//unit) & 
--       (one//β[0] -> two//unit)
--     )
--   ) = _ in 
--   y[0](one;;)
--   ]

--   -- expected: cons//nil//unit
--   #eval infer_reduce 0 [lessterm|
--     let _ : [_<:⟨nat_⟩] β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} = _ in 
--     (y[0] (succ;zero;;))
--   ]

--   -- NOTE: weakening causes a fairly imprecise type  
--   -- expected:  {2 // β[1] with β[0] * β[1] <: ⟨nat_list⟩}  
--   #eval infer_reduce 10 [lessterm|
--     let _ : [_] β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} = _ in 
--     (y[0] (succ;zero;;))
--   ]

-- ---------------------------------------------------------------
--   ----------------------------------
--   -- incomplete
--   -- nat should not be subbed into relational key
--   -- double
--   #eval infer_reduce 10 [lessterm|
--     let _ : ⟨nat_⟩ = _ in
--     let _ = fix(_ => _ => (match (y[0]) 
--       case zero;; => zero;;
--       case succ;y[0] => succ;succ;(y[2](y[0]))
--     )) in
--     y[0](y[1])
--   ]
--   ----------------------------------

--   --------- relational typing -----------

--   -- complete: relational type with base case and inductive case 
--   #eval infer_reduce 0 [lessterm|
--     fix(_ => _ => match y[0] 
--     case zero;; => nil;;
--     case succ;y[0] => cons;(y[2](y[0]))
--     )
--   ]

--   #eval infer_reduce 0 [lessterm|
--     let _ = fix(_ => _ => match y[0]
--       case zero;; => nil;;
--       case succ;y[0] => cons;(y[2](y[0]))
--     ) in 
--     y[0]
--   ]

--   --------- relational selection -----------

--   #eval unify_reduce 10 
--   [lesstype| (succ//zero//unit * α[0]) ]
--   [lesstype| ⟨nat_list⟩ ]
--   [lesstype| α[0] ]

--   #eval unify_reduce 10 
--   [lesstype| (succ//succ//zero//unit * α[0]) ]
--   [lesstype| ⟨nat_list⟩ ]
--   [lesstype| α[0] ]

--   -- expected: cons//(thing//unit * cons//(thing//unit * nil//unit))
--   #eval unify_reduce 10 
--   [lesstype| (succ//succ//zero//unit * α[7]) ]
--   [lesstype|
--       (induct ((zero//unit * nil//unit) |
--           {(succ//β[1] * cons//(thing//unit * β[0])) with (β[1] * β[0]) <: β[2] # 2}))
--   ]
--   [lesstype| (α[7]) ]


--   -- NOTE: it is important to preserve the universal type structure for application to succeed
--   -- expected: cons//(thing//unit * cons//(thing//unit * nil//unit))
--   #eval infer_reduce 10 [lessterm|
--     (_ => fix(_ => _ => match y[0] 
--       case zero;; => nil;;
--       case succ;y[0] => cons;(y[3], y[2](y[0]))
--     ))(thing;;)(succ;succ;zero;;)
--   ]

--   -- expected: cons//(thing//unit * cons//(thing//unit * nil//unit))
--   #eval infer_reduce 10 [lessterm|
--     let _ = (_ => fix(_ => _ => match y[0]
--       case zero;; => nil;;
--       case succ;y[0] => cons;(y[3], y[2](y[0]))
--     )) in 
--     y[0](thing;;)(succ;succ;zero;;)
--   ]


--   -- expected: cons//nil//unit
--   #eval infer_reduce 10 [lessterm|
--     fix(_ => _ => match y[0]
--       case zero;; => nil;;
--       case succ;y[0] => cons;(y[2](y[0]))
--     )(succ;zero;;)
--   ]
  
--   -- expected: cons//nil//unit
--   #eval infer_reduce 10 [lessterm|
--     let _ = fix(_ => _ => match y[0]
--       case zero;; => nil;;
--       case succ;y[0] => cons;(y[2](y[0]))
--     ) in 
--     y[0](succ;zero;;)
--   ]

--   -- expected: cons//cons//nil//unit
--   #eval infer_reduce 10 [lessterm|
--     let _ = fix(_ => _ => match y[0]
--       case zero;; => nil;;
--       case succ;y[0] => cons;(y[2](y[0]))
--     ) in 
--     y[0](succ;succ;zero;;)
--   ]


--   #eval unify_reduce 10 
--   [lesstype|
--   ([_<:α[3]] (β[0] -> {β[0] with (β[1] * β[0]) <: 
--     (induct (
--         (zero//unit * nil//unit) | 
--         {(succ//β[1] * cons//β[0]) with (β[1] * β[0]) <: β[2] # 2}))
--    # 1}))
--   ]
--   [lesstype| succ//zero//unit -> α[0] ]
--   [lesstype| α[0] ]

--   -------------------------------

--   #eval infer_reduce 0 [lessterm| 
--       (fix (_ => _ => match y[0] 
--         case (zero;;, y[0]) => true;;  
--         case (succ;y[0], succ;y[1]) => y[4](y[0], y[1])
--         case (succ;y[0], zero;;) => false;; 
--       ))
--   ] 

--   -- sound
--   -- expected: none  
--   #eval infer_reduce 0 [lessterm| 
--     let _ : succ//zero//unit = (_ => match y[0] case (y[0], y[1]) => 
--       (
--         if 
--           (fix (_ => _ => match y[0]
--             case (zero;;, y[0]) => true;;  
--             case (succ;y[0], succ;y[1]) => y[4](y[0], y[1])
--             case (succ;y[0], zero;;) => false;; 
--           ) (y[0], y[1]))
--         then y[1] else y[0]
--       )
--     ) in
--     (y[0] (succ;succ;zero;;, succ;zero;;))
--   ] 

--   -- expected: none
--   #eval infer_reduce 0 [lessterm| 
--     let _ = (_ => match y[0] case ; => ;)(zero;;) in
--     y[0]
--   ] 

--   ---------- generics ----------------

--   #eval infer_reduce 10 [lessterm|
--     (_ => match y[0] case cons;(y[0], y[1]) => y[0])(cons;(ooga;;, booga;;))
--   ]

--   #eval infer_reduce 10 [lessterm|
--     let _ = _ => match y[0] case cons;(y[0], y[1]) => y[0] in
--     y[0](cons;(ooga;;, booga;;))
--   ]

--   #eval infer_reduce 10 [lessterm|
--     let _ = _ => match y[0] case cons;(y[0], y[1]) => y[0] in 
--     y[0]  
--   ]

--   #eval infer_reduce 10 [lessterm|
--     let _ : [_][_] cons//(β[0] * β[1]) -> β[0] = _ in
--     (y[0] (cons;(ooga;;, booga;;)))  
--   ]

--   ---------- expanding return type ----------------
--   -- weakening mechanism may be superfluous; subsumed by behavior of inductive and existential types.
--   ----------------------------------------------
--   -- object-oriented example without type annotation ----------------
--   -- a typical object-oriented pattern:
--   -- where the method constructs new data and calls constructor with new data 

--   -- expected:
--   /-
--   constructor : (Data <: ?) >> Data -> {Object with Data * Object <: DO}
--         where μ DO . {D, α, O // D * (data : D & update : α -> O) with (cons//(α * D) * O) <: DO
--   -/
--   #eval infer_reduce 0 [lessterm|
--     -- fix \ self \ data => 
--     fix (_ => _ => 
--       (
--         @data = y[0]
--         @update = (_ => y[2](cons;(y[0], y[1])))
--       )
--     ) 
--   ]

-- -- NOTE: 
-- -- The weakening flag may not actually be needed, as distinct types can be handled via existential inside of inductive type,
-- -- which results in fresh variables at the time of unification.
--   /-
-- (? >> 

-- (β[1] >> -- this is correct; short hand for (β[0] <: β[1] >>) 

-- (β[0] ->
--    {1 // β[0] with (β[1] * β[0]) <: (induct 
--       {3 // (β[2] * (
--         (data : β[2]) & (update : (β[1] -> β[0]))
--         )) with (cons//(β[1] * β[2]) * β[0]) <: β[3]}
--    )}
--  )
--  )
--  )
--   -/


-- -- diverges
-- -- non-termination without let generalization
-- /-
--   #eval infer_reduce 0 [lessterm|
--     -- fix \ self \ data => 
--     let _ = fix (\ y[0] => \ y[0] => 
--       (@update = (\ y[0] => (y[2] cons;(y[0], y[1]))))
--     ) in 
--     -- y[0]
--     -- let _ = (y[1] nil;;)
--     (y[0] nil;;)
--     -- (((y[0] nil;;).update #hello()).update #world())
--   ]
-- -/
--   ------------------


--   ----------------------------------------
--   -- weakening mechanism is deprecated
--   ----------------------------------------
--   -- #eval infer_reduce 0 [lessterm|
--   --   let _ : ? >> β[0] -> (β[0] -> (β[0] * β[0])) = _ in 
--   --   ((y[0] #hello ()) #world ())
--   -- ]

--   -- #eval infer_reduce 0 [lessterm|
--   --   let _ = (\ y[0] => \ y[0] => (y[1], y[0])) in 
--   --   ((y[0] #hello ()) #world ())
--   -- ]

--   -- #eval infer_reduce 0 [lessterm|
--   --   (((\ y[0] => \ y[0] => (y[1], y[0])) #hello ()) #world ())
--   -- ]

--   -- -- NOTE: this requires subbing in unions to maintain weakening after let-poly generalization
--   -- #eval infer_reduce 0 [lessterm|
--   --   let _ : ? >> β[0] -> (β[0] -> (β[0] * β[0])) = _ in 
--   --   let _ = (y[0] #hello ()) in
--   --   (y[0] #world())
--   -- ]
--   ----------------------------------------

--   ---------- strengthening ----------------
--   #eval infer_reduce 0 [lessterm|
--   let _ : uno//unit -> unit = _ in 
--   let _ : dos//unit -> unit = _ in 
--   (_ => y[2](y[0]))
--   ]

--   #eval infer_reduce 0 [lessterm|
--   let _ : uno//unit -> unit = _ in 
--   let _ : dos//unit -> unit = _ in 
--   (_ => y[2](y[0]))(uno;;)
--   ]

--   #eval infer_reduce 0 [lessterm|
--   let _ : uno//unit -> unit = _ in 
--   y[0](uno;;)
--   ]

--   -- expected: (uno : unit) & (dos : unit) -> unit * unit
--   #eval infer_reduce 0 [lessterm|
--     let _ : (uno : unit) -> unit = _ in 
--     let _ : (dos : unit) -> unit = _ in 
--     (_ => 
--       y[2](y[0]), y[1](y[0])
--     )
--   ]

--   -- expected: ⊥ -> unit * unit
--   #eval infer_reduce 0 [lessterm|
--   let _ : uno//unit -> unit = _ in 
--   let _ : dos//unit -> unit = _ in 
--   (_ => (y[2](y[0]), y[1](y[0])))
--   ]

--   #eval infer_reduce 0 [lessterm|
--   let _ : uno//unit -> unit = _ in 
--   let _ = _ in 
--   let _ = y[1](y[0]) in 
--   y[0]
--   ]

--   #eval infer_reduce 0 [lessterm|
--   let _ : uno//unit -> unit = _ in 
--   let _ : dos//unit -> unit = _ in 
--   (_ =>
--     let _ = y[2](y[0]) in 
--     let _ = y[2](y[1]) in 
--     (y[0], y[1])
--   )
--   ]

--   ----------------------------------
--   #eval [lessterm| @x = hello;; @y = world;;]
--   --------------------------------------

--   #eval unify_decide 0 
--     [lesstype| hello//unit ] 
--     [lesstype| α[0] ] 

--   -- not well foundend: induction untagged 
--   -- expected: false
--   #eval unify_decide 0 
--     [lesstype| hello//unit ] 
--     [lesstype| induct wrong//unit | β[0] ] 

--   -- potentially diverges - inductive type not well founded
--   -- expected: false
--   #eval unify_decide 0 
--     [lesstype| hello//unit ] 
--     [lesstype| induct β[0] ] 

--   def bad_nat_list := [lesstype| 
--     induct 
--       (zero//unit * nil//unit) | 
--       {(β[0] * β[1]) with β[0] * β[1] <: β[2]}
--   ]

--   -- expected: false
--   #eval unify_decide 0 
--     [lesstype| zero//unit * nil//unit ] 
--     bad_nat_list

--   def other_nat_list := [lesstype| 
--     induct {(succ//β[0] * cons//β[1]) with β[0] * β[1] <: β[2]}
--   ]

--   -- expected: false; base case is missing
--   #eval unify_decide 0 
--     [lesstype| succ//zero//unit * cons//nil//unit ] 
--     other_nat_list

--   #eval infer_reduce 10 [lessterm|
--   fix(_ => _ => match y[0]  
--     case (succ;y[0], succ;y[1]) => y[3](y[0], y[1])
--     case (zero;;, y[0]) => y[0]
--     case (y[0], zero;;) => y[0] 
--   )
--   ]

--   -- NOTE: requires simplification when checking if relation is reducible 
--   -- expected: the difference: succ//zero//unit
--   #eval infer_reduce 10 [lessterm|
--   fix(_ => _ => match y[0]  
--     case (succ;y[0], succ;y[1]) => y[3](y[0], y[1])
--     case (zero;;, y[0]) => y[0]
--     case (y[0], zero;;) => y[0] 
--   )(succ;succ;zero;;, succ;succ;succ;zero;;)
--   ]

--   -- expected: the difference: succ//zero//unit
--   #eval unify_reduce 10
--   [lesstype|
--   ([_<:{(β[1] ->
--     β[0]) with (β[1] * β[0]) <: (induct ({((succ//β[1] * succ//β[2]) * β[0]) with ((β[1] * β[2]) * β[0] & top) <: β[3] # 3} |
--       ({((zero//unit * β[0]) * β[0]) # 1} | {((β[0] * zero//unit) * β[0]) # 1} | bot))) # 2}] β[0])
--   ]
--   [lesstype| succ//zero//unit * succ//succ//zero//unit -> α[7] ]
--   [lesstype| α[7] ] 

--   ----------------------------------

--   def gt := [lesstype| 
--     induct  
--       {succ//β[0] * zero//unit} | 
--       {succ//β[0] * succ//β[1] with (β[0] * β[1]) <: β[2]}
--   ]

--   -------------------------------------------------

--   def spec := [lesstype| 
--   (α[0] * α[1]) -> (
--     { β[0] with (x:β[0] & y:α[1] & z:α[0]) <: ⟨plus⟩} |
--     { β[0] with (x:β[0] & y:α[0] & z:α[1]) <: ⟨plus⟩}
--   )  
--   ]

--   -- Note: is this in effect, the same thing as PDR/IC3?
--   -- That is, whatever is learned to strengthen the conclusion 
--   -- is automatically applied to preceding iterations 
--   -- due to the wrapping type in inductive binding 
--   -- NOTE: this may have some non-termination depending on how occurs is used 
--   #eval infer_simple 10 
--   [lessterm|
--   let _ : ⟨spec⟩ = fix(_ => _ => match y[0]  
--     case (succ;y[0], succ;y[1]) => y[3](y[0], y[1])
--     case (zero;;, y[0]) => y[0]
--     case (y[0], zero;;) => y[0] 
--   ) in 
--   y[0]
--   ]

--   -------------------------------------------------

--   #eval infer_reduce 10 
--   [lessterm|
--   let _ = fix(_ => _ => match y[0]
--     case (succ;y[0], succ;y[1]) => (y[3] (y[0], y[1]))
--     case (zero;;, y[0]) => y[0]
--     case (y[0], zero;;) => y[0] 
--   ) in 
--   y[0]
--   ]

--   -- expected: succ//zero//unit 
--   #eval infer_reduce 10 
--   [lessterm|
--   let _ = fix(_ => _ => match y[0]
--     case (succ;y[0], succ;y[1]) => (y[3] (y[0], y[1]))
--     case (zero;;, y[0]) => y[0]
--     case (y[0], zero;;) => y[0] 
--   ) in 
--   y[0](succ;succ;zero;;, succ;zero;;)
--   ]

--   def diff_rel :=
--   [lesstype|
--     induct 
--       {zero//unit * β[0] * β[0]} | 
--       {β[0] * zero//unit * β[0]} |
--       {(succ//β[1] * succ//β[2] * β[0]) with (β[1] * β[2] * β[0]) <: β[3]}
--   ]

--   #eval unify_reduce 10
--   [lesstype| succ//succ//zero//unit * succ//zero//unit * α[0] ]
--   diff_rel
--   [lesstype| α[0] ]



--   def plus_choice := [lesstype| 
--   α[0] * α[1] * (
--     { β[0] with (x:β[0] & y:α[1] & z:α[0]) <: ⟨plus⟩} |
--     { β[0] with (x:β[0] & y:α[0] & z:α[1]) <: ⟨plus⟩}
--   )  
--   ]

--   #eval unify_reduce 10
--   plus_choice
--   diff_rel
--   [lesstype| α[0] ]


--   -- #eval unify_reduce 10
--   -- [lesstype|
--   --   ? >> β[0] -> {β[0] with (β[1] * β[0]) <: ⟨diff_rel⟩}
--   -- ]
--   -- spec
--   -- [lesstype| α[0] * α[1] ]

--   ------------ factoring checking ----------------

--   def list_ := [lesstype|
--     induct 
--       nil//unit |
--       cons//β[0]
--   ]

--   -- #eval [lessterm| 
--   --   let _ : ⟨nat_⟩ -> ⟨list_⟩ = fix(\ y[0] =>
--   --     \ zero;; => nil;;  
--   --     \ succ;y[0] => cons;(y[1] y[0]) 
--   --   )
--   --   in
--   --   y[0]
--   -- ] 

--   -- #eval infer_reduce 0 [lessterm| 
--   --   fix(\ y[0] =>
--   --     \ zero;; => nil;;  
--   --     \ succ;y[0] => cons;(y[1] y[0]) 
--   --   )
--   -- ]



--   -- expected: true 
--   #eval unify_decide 0
--   [lesstype| ⟨nat_list⟩ ]
--   [lesstype| ⟨nat_⟩ * ⟨list_⟩ ]

--   -- expected: false 
--   #eval unify_decide 0
--   [lesstype| ⟨nat_list⟩ ]
--   [lesstype| ⟨nat_⟩ * ⟨nat_⟩ ]

--   -- expected: false 
--   #eval unify_decide 0
--   [lesstype| ⟨nat_list⟩ ]
--   [lesstype| ⟨nat_⟩ * nil//unit ]

--   -- expected: false
--   #eval unify_decide 0
--   [lesstype| ⟨nat_⟩ * ⟨list_⟩ ]
--   [lesstype| ⟨nat_list⟩ ]


--   ----- factored construction ----
  
--   -- expected: ⟨nat_⟩ * ⟨list_⟩
--   #eval unify_reduce 10
--   [lesstype| ⟨nat_list⟩ ]
--   [lesstype| α[1] * α[2] ]
--   [lesstype| α[1] * α[2] ]

--   -- expected: ⟨list_⟩
--   #eval unify_reduce 10
--   [lesstype| ⟨nat_list⟩ ]
--   [lesstype| ⟨nat_⟩ * α[0] ]
--   [lesstype|  α[0] ]

--   #eval unify_decide 10
--   [lesstype| {β[0] with β[0] * α[0] <: ⟨nat_list⟩} ]
--   [lesstype| top ]


--   ----- factored projection ----

--   -- sound
--   -- expected: false 
--   #eval unify_decide 10
--   [lesstype| {β[0] -> unit with β[0] * β[1] <: ⟨nat_list⟩ # 2} ]
--   [lesstype| succ//zero//unit -> unit ]

--   -- unsound
--   -- expected: false 
--   #eval unify_decide 10
--   [lesstype| {β[0] -> unit with β[0] * β[1] <: ⟨nat_list⟩ # 2} ]
--   [lesstype| ⟨nat_⟩ -> unit ]

--   -- expected: false 
--   #eval unify_decide 10
--   [lesstype| {β[0] -> unit with β[0] * cons//cons//nil//unit <: ⟨nat_list⟩ # 2} ]
--   [lesstype| ⟨nat_⟩ -> unit ]

--   -- expected: false 
--   #eval unify_decide 10
--   [lesstype| {β[0] with β[0] * α[0] <: ⟨nat_list⟩} ]
--   [lesstype| succ//zero//unit ]

--   -- expected: true 
--   #eval unify_decide 10
--   [lesstype| {β[0] with β[0] * α[0] <: ⟨nat_list⟩} ]
--   [lesstype| ⟨nat_⟩ ]

--   -- expected: true 
--   #eval unify_decide 10
--   [lesstype| {β[0] with β[0] * β[1] <: ⟨nat_list⟩ # 2} ]
--   [lesstype| ⟨nat_⟩ ]

--   -- expected: false
--   #eval unify_decide 10
--   [lesstype| {β[0] with β[0] * β[1] <: ⟨nat_list⟩ # 2} ]
--   [lesstype| succ//zero//unit ]

--   ----------------------------

--   -- expected: true 
--   #eval unify_decide 10
--   [lesstype| {β[0] with α[1] * β[0] <: ⟨nat_list⟩} ]
--   [lesstype| ⟨list_⟩ ]

--   -- expected: false 
--   #eval unify_decide 10
--   [lesstype| {β[0] with β[0] * α[0] <: ⟨nat_list⟩} ]
--   [lesstype| succ//succ//zero//unit ]

--   -- incomplete 
--   -- expected: true 
--   #eval unify_decide 10
--   [lesstype| [_<:⟨nat_⟩] β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} ]
--   [lesstype| ⟨nat_⟩ -> ⟨list_⟩ ]

--   -- expected: true 
--   #eval unify_decide 10
--   [lesstype| [_] β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩ # 2} ]
--   [lesstype| ⟨nat_⟩ -> ⟨list_⟩ ]

--   -- NOTE: the relational constraint check should check inhabitation 
--   -- [a <: Nat]{b with a * b <: nat_list} is inhabited
--   -- this requires unifying the left universal's constraint first, rather than backwards
--   -- and also checking inhabitation, use factoring to check inhabitation
--   -- X * Y <: ⟨nat_list⟩ |-  (X -> Y) <: NAT -> LIST
--   -- complete
--   -- expected: true 
--   #eval unify_decide 10
--   [lesstype| [_<:{β[1] -> β[0] with β[1] * β[0] <: ⟨nat_list⟩ # 2}] β[0] ]
--   [lesstype| ⟨nat_⟩ -> ⟨list_⟩ ]

--   -- expected: true 
--   #eval unify_decide 10
--   [lesstype| {β[1] * β[0] with β[1] * β[0] <: ⟨nat_list⟩ # 2} ]
--   [lesstype| ⟨nat_⟩ * ⟨list_⟩ ]

--   -- incomplete
--   -- expected: true 
--   #eval unify_decide 10
--   [lesstype| [_<:{β[1] -> β[0] with β[1] * β[0] <: ⟨nat_list⟩ # 2}] β[0] ]
--   [lesstype| [_<:⟨nat_⟩] β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} ]


--   -- expected: true 
--   #eval unify_decide 10
--   [lesstype| [_<:⟨nat_⟩] β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} ]
--   [lesstype| succ//zero//unit -> α[0] ]

--   -- expected: false 
--   #eval unify_decide 0
--   [lesstype| ⟨nat_⟩ -> ⟨list_⟩ ]
--   [lesstype| [_<:⟨nat_⟩] β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} ]

--   -- expected: false 
--   #eval unify_decide 10
--   [lesstype| ⟨nat_⟩ -> ⟨list_⟩ ]
--   [lesstype| α[0] -> {β[0] with α[0] * β[0] <: ⟨nat_list⟩} ]

--   -- expected: false 
--   #eval unify_decide 10
--   [lesstype| ⟨list_⟩ ]
--   [lesstype| {β[0] with α[0] * β[0] <: ⟨nat_list⟩} ]

--   -- expected: false
--   #eval unify_decide 10
--   [lesstype| α[0] * ⟨list_⟩ ]
--   [lesstype| ⟨nat_list⟩ ]

--   -- expected: true 
--   #eval unify_decide 10
--   [lesstype| {β[0] with β[0] <: ⟨list_⟩} ]
--   [lesstype| ⟨list_⟩ ]


--   ------------------------------


--   -- expected: true 
--   #eval unify_decide 0
--   [lesstype| ⟨nat_⟩ ]
--   [lesstype|
--     induct
--       zero//unit |
--       {succ//β[0] with β[0] <: β[2] # 2}
--   ]

-- ---------------- debugging

--   #eval infer_reduce 0 [lessterm| 
--     let _ : ⟨nat_⟩ -> ⟨list_⟩ = fix(_ => _ => match y[0]
--       case zero;; => nil;;  
--       case succ;y[0] => cons;(y[2](y[0])) 
--     )
--     in
--     y[0]
--   ] 
--   --------------------------------

--   ------- proactive safely assgined ---------

--   -- expected: false 
--   #eval unify_decide 0
--   [lesstype| {β[0]} ]
--   [lesstype|  ooga//unit ]

--   -- expected: false 
--   #eval unify_decide 0
--   [lesstype| {β[0] with β[0] <: ooga//unit} ]
--   [lesstype|  booga//unit]

--   -- expected: false 
--   #eval unify_decide 0
--   [lesstype| {β[2] with β[0] * β[1] <: ⟨nat_list⟩ # 3} ]
--   [lesstype| ⟨nat_⟩]

--   -- expected: true 
--   #eval unify_decide 0
--   [lesstype| {β[0] with β[0] <: ooga//unit} ]
--   [lesstype|  ooga//unit | booga//unit]

--   -- expected: false
--   #eval unify_decide 0
--   [lesstype| {β[0] with β[0] <: (three//unit)} ]
--   [lesstype| one//unit ]

--   -- expected: false
--   #eval unify_decide 0
--   [lesstype| (one//unit | three//unit) ]
--   [lesstype| one//unit ]

--   -- expected: false
--   #eval unify_decide 0
--   [lesstype| {β[0] with β[0] <: (one//unit | three//unit)} ]
--   [lesstype| one//unit ]

--   -- expected: false 
--   #eval unify_decide 0
--   [lesstype| (one//unit * two//unit) | (three//unit * four//unit) ]
--   [lesstype| (three//unit * four//unit)  ]

--   -- expected: false 
--   #eval unify_decide 0
--   [lesstype| {β[0] with β[0] <: (one//unit * two//unit) | (three//unit * four//unit)} ]
--   [lesstype| one//unit * two//unit ]

--   -- expected: false 
--   #eval unify_decide 0
--   [lesstype| {β[0]  with β[0] * β[1] <: (one//unit * two//unit) | (three//unit * four//unit) # 2} ]
--   [lesstype| one//unit ]

--   -- expected: false 
--   #eval unify_decide 10
--   [lesstype| {β[0] with β[0] * α[0] <: (one//unit * two//unit) | (three//unit * four//unit)} ]
--   [lesstype| one//unit  ]

--   -- expected: false 
--   #eval unify_decide 0
--   [lesstype| {β[0] with β[0] * β[1] <: (one//unit * two//unit) | (three//unit * four//unit) # 2} ]
--   [lesstype| one//unit ]

--   -- expected: true 
--   #eval unify_decide 0
--   [lesstype| {β[0] with β[0] * β[1] <: (one//unit * two//unit) | (three//unit * four//unit) # 2} ]
--   [lesstype| one//unit | three//unit ]

--   -- expected: false 
--   #eval unify_decide 0
--   [lesstype| (one//unit * two//unit) | (three//unit * four//unit) ]
--   [lesstype| one//unit  ]

--   -- expected: true 
--   #eval unify_decide 10 
--   [lesstype| {β[0] with β[0] * α[0] <: (one//unit * two//unit) | (three//unit * four//unit)} ]
--   [lesstype| one//unit | three//unit  ]

--   -- expected: false 
--   #eval unify_decide 10 
--   [lesstype| {β[0] with β[0] * α[0] <: (one//unit * two//unit) | (three//unit * four//unit)} ]
--   [lesstype| one//unit  ]



-- --------------------- universal introduction subtyping ----------------

--   -- expected: false 
--   #eval unify_decide 0
--   [lesstype| one//unit  ]
--   [lesstype| [_<:{(β[0] | α[0]) -> β[0] with (β[0] | α[0]) <: (one//unit | two//unit) & (three//unit | four//unit) }] β[0] ]

--   -- expected: false 
--   #eval unify_decide 0
--   [lesstype| one//unit  ]
--   [lesstype| (one//unit | two//unit) & (three//unit | four//unit) ]

--   -- expected: false 
--   #eval unify_decide 0
--   [lesstype| one//unit  ]
--   [lesstype|  [_<:{(β[0] | α[0]) -> β[0] with (β[0] | α[0]) <: (one//unit | two//unit) * (three//unit | four//unit)}] β[0] ]

--   -- expected: false 
--   #eval unify_decide 0
--   [lesstype| one//unit  ]
--   [lesstype| (one//unit | two//unit) * (three//unit | four//unit) ]


-- ---------------------------------
--   #eval infer_reduce 1 [lessterm| 
--     let _ : α[0] = _ in
--     y[0] 
--   ] 

--   def ooga := [lesstype| 
--     induct
--       {zero//unit * β[0]} |
--       {succ//β[0] * succ//β[1] with β[0] * β[1] <: β[2]}
--   ]

--   #eval unify_reduce 10
--   [lesstype| α[2] * α[3] -> {β[0] with (α[2] * β[0]) * (α[3] * β[0]) <: ⟨ooga⟩ * ⟨ooga⟩} ]
--   [lesstype| α[0] * α[1] -> α[1] ]
--   [lesstype| hmm//unit ]


-- --------------------------------------------------------

--   -- expected: none 
--   #eval infer_reduce 0 [lessterm| 
--     let _ : ([_][_] β[0] * β[1] -> {β[0] with (β[0] * β[1]) <: ⟨nat_⟩ * ⟨nat_⟩ # 1}) = 
--     (_ => match y[0] case (y[0], y[1]) => y[0]) in
--     y[0]
--   ] 

-- ------- argument type inference ------

--   -- expected: the argument type should be refined by the function application 
--   -- should be similar to the function type, but just an exisitential without the return type
--   -- the return type is inferred, but the argument type is not inferred 
--   -- e.g.
--   /-
--     ({2 // β[0] with (β[0] * β[1]) <: (induct (
--           (zero//unit * nil//unit) |
--           {2 // (succ//β[1] * cons//β[0]) with (β[1] * β[0]) <: β[2]}
--     ))})
--   -/
--   #eval unify_reduce 50
--   [lesstype| 
--   ([_<:α[10]] (β[0] ->
--   {β[0] with (β[1] * β[0]) <: (induct ((zero//unit * nil//unit) |
--      {(succ//β[1] * cons//β[0]) with (β[1] * β[0]) <: β[2] # 2})) # 1}))
--   ]
--   [lesstype| α[20] -> α[12]]
--   [lesstype| α[20]]


--   -- expected: the argument type should be refined by the function application 
--   -- e.g.
--   /-
--     ({2 // β[0] with (β[0] * β[1]) <: (induct (
--           (zero//unit * nil//unit) |
--           {2 // (succ//β[1] * cons//β[0]) with (β[1] * β[0]) <: β[2]}
--     ))})
--   -/
--   #eval infer_reduce 0 [lessterm| 
--     let _ = fix (_ => _ => match y[0]
--       case (zero;;) => nil;;  
--       case (succ;y[0]) => cons;(y[1](y[0])) 
--     ) in
--     let _ = _ in
--     let _ = (y[1] (y[0])) in
--     y[1]
--   ] 

-- --------------------------------------

--   ----------------------------
--   -- incomplete without model-based subtyping / semantic subtyping
--   ----------------------------
--   -- URL: https://pnwamk.github.io/sst-tutorial/#%28part._sec~3asemantic-subtyping%29
--   #eval unify_decide 0
--   [lesstype| (x//unit | y//unit) * y//unit ] 
--   [lesstype| (x//unit * y//unit) | (y//unit * y//unit) ] 

--   -------------------------

--   -- expected: (?spanish unit | ?english unit)
--   #eval infer_reduce 10 [lessterm|
--     let _ : [_<:α[0]] β[0] -> {β[0] with β[1] * β[0] <: (uno//unit * dos//unit) | (one//unit * two//unit)} = _ in
--     let _ : α[1] = _ in
--     (
--       (_ => match y[0] case dos;; => spanish;; case two;; => english;;)
--       (y[1](y[0]))
--     ) 
--   ]

--   -----------  argument type strengthening ----------

--   -- expected: uno//unit
--   #eval infer_reduce 10 [lessterm|
--     let _ : uno//unit -> dos//unit = _ in
--     let _ = _ in
--     let _ = y[1](y[0]) in
--     y[1]
--   ]

--   -- expected: uno//unit
--   #eval infer_reduce 10 [lessterm|
--     let _ : [_] β[0] -> {β[0] with β[1] * β[0] <: (uno//unit * dos//unit)} = _ in
--     let _ = _ in
--     (
--       (_ => match y[0] case dos;; => y[0])
--       (y[1](y[0]))
--     ) 
--   ]

--   -- expected: uno//unit
--   #eval infer_reduce 10 [lessterm|
--     let _ : uno//unit -> dos//unit = _ in
--     let _ = _ in
--     (
--       (_ => match y[0] case dos;; => y[0])
--       (y[1](y[0]))
--     ) 
--   ]

--   -- requires local strengthening in left-existential
--   -- expected: uno//unit
--   #eval infer_reduce 10 [lessterm|
--     let _ : [_<:α[2]] β[0] -> {β[0] with β[1] * β[0] <: (uno//unit * dos//unit)} = _ in
--     let _ = _ in
--     (
--       (_ => match y[0] case dos;; => y[0])
--       (y[1](y[0]))
--     ) 
--   ]

--   -- incomplete
--   -- expected: uno//unit | other//unit
--   #eval infer_reduce 10 [lessterm|
--     let _ : [_] β[0] -> {β[0] with β[1] * β[0] <: (uno//unit * dos//unit) | (one//unit * two//unit)} = _ in
--     let _ = _ in
--     (
--       (_ => match y[0] case dos;; => y[0] case two;; => other;;)
--       (y[1](y[0]))
--     ) 
--   ]

--   -- incomplete
--   -- expected: dos//unit | other//unit
--   #eval infer_reduce 10 [lessterm|
--     let _ : (dos//unit) | (two//unit) = _ in
--     (_ => match y[0] case dos;; => y[0] case two;; => other;;)
--     (y[0])
--   ]

--   -- incomplete
--   -- expected: uno//unit 
--   #eval infer_reduce 10 [lessterm|
--     let _ : [_] β[0] -> {β[0] with β[1] * β[0] <: (uno//unit * dos//unit) | (one//unit * two//unit)} = _ in
--     let _ = _ in
--     (
--       (_ => match y[0] case dos;; => y[0] case two;; => uno;;)
--       (y[1](y[0]))
--     ) 
--   ]


--   -----------  local strengthening ----------

--   -- complete
--   -- expected: (one//unit | three//unit) 
--   #eval infer_reduce 0 [lessterm|
--     let _ = _ in
--     let _ = (
--       (_ => match y[0] case one;; => two;; case three;; => four;;)
--       (y[0])
--     ) in
--     y[1]
--   ]

--   -- expected: (two//unit | four//unit)
--   #eval infer_reduce 0 [lessterm|
--     let _ = _ in
--     (_ => match y[0] case one;; => two;; case three;; => four;;)
--     (y[0])
--   ]

--   -- expected:  (([_:(one//unit -> two//unit)]β[0]) & ([_:(three//unit -> four//unit)]β[0]))
--   #eval infer_reduce 0 [lessterm|
--     _ => (
--       (_ => match y[0] 
--         case one;; => two;; 
--         case three;; => four;;
--       )
--       (y[0])
--     )
--   ]

--   -- expected: one//unit
--   #eval infer_reduce 0 [lessterm|
--     let _ = _ in
--     (
--       (_ => match y[0] 
--         case one;; => y[0] 
--         case three;; => one;;
--       )
--       (y[0])
--     )
--   ]

--   -- expected: none 
--   #eval infer_reduce 0 [lessterm|
--     let _ : one//unit | two//unit = _ in
--     (
--       (_ => match y[0] 
--         case one;; => y[0] 
--         case three;; => one;;
--       )
--       (y[0])
--     )
--   ]

--   -----------  implication existential ----------

--   -- incomplete
--   -- expected: unit 
--   #eval unify_reduce 10 
--   [lesstype| (one//unit -> unit) & (three//unit -> unit) ]
--   [lesstype| {β[0] with β[0] <: (one//unit | three//unit)} -> α[7] ]
--   [lesstype| α[7] ]

--   -- expected: none 
--   #eval unify_reduce 10 
--   [lesstype| {β[0] with β[0] <: (one//unit | three//unit)} ]
--   [lesstype| one//unit ]
--   [lesstype| unexpected//unit ]


--   -- incomplete
--   -- expected: one//unit 
--   #eval infer_reduce 0 [lessterm|
--     let _ : {β[0] with β[0] <: one//unit | three//unit} = _ in
--     (
--       (_ => match y[0] 
--         case one;; => y[0] 
--         case three;; => one;;
--       )
--       (y[0])
--     )
--   ]

--   -- incomplete
--   -- expected: one//unit | three//unit 
--   #eval infer_reduce 0 [lessterm|
--     let _ : {β[0] with β[0] <: one//unit | three//unit} = _ in
--     (
--       (_ => match y[0] 
--         case one;; => y[0] 
--         case three;; => y[0]
--       )
--       (y[0])
--     )
--   ]


--   ---------- implication union ---------
--   -- (S1 -> T) & (S2 -> T) <: (S1 | S2 -> T) 


--   -- expected: unit
--   #eval unify_reduce 10 
--   [lesstype| (one//unit -> unit) & (three//unit -> unit) ]
--   [lesstype| (one//unit | three//unit) -> α[7] ]
--   [lesstype| α[7] ]


--   -- complete
--   -- expected: four//unit
--   #eval infer_reduce 0 [lessterm|
--     let _ : one//unit | three//unit = _ in
--     (
--       (_ => match y[0] 
--         case one;; => four;; 
--         case three;; => four;;
--       )
--       (y[0])
--     )
--   ]

--   -- expected: two//unit * four//unit
--   #eval unify_reduce 10 
--   [lesstype| (one//unit -> two//unit) & (three//unit -> four//unit) ]
--   [lesstype| (one//unit -> α[7]) & (three//unit -> α[8])]
--   [lesstype| α[7] * α[8] ]


--   -- NOTE: requires adjustment to be turned on
--   -- expected: two//unit | four//unit
--   #eval unify_reduce_adj (empty.insert 7) 10
--   [lesstype| (one//unit -> two//unit) & (three//unit -> four//unit) ]
--   [lesstype| (one//unit | three//unit) -> α[7] ]
--   [lesstype| α[7] ]
--   /-
--   -- TODO: adjustment isn't necessary if it treats variable as unassigned for each case 
--   -/
--   ----------------------
--   /-
--                                                       Y <: ?'
--                                                   --------------
--                                                     Y <: B | ?'
--                                                   --------------------
--     B <: ?                                            Y <: ?
-- ------------------------                     ------------------------
--   (A -> B) <: (A -> ?)                         (X -> Y) <: (X -> ?) 
-- ---------------------------------          -----------------------------------
--   (A -> B & X -> Y) <: (A -> ?),            (A -> B & X -> Y) <: (X -> ?)
-- --------------------------------------------------------------------------------
--   (A -> B & X -> Y) <: (A | X) -> ?


--   -- NOTE: requires expanding ? into B | Y
--   -- since it starts as a variable; union a variable to indicate it can expand 
--   -/

-- -----------------

--   -- NOTE: variable α[7] should not be refined
--   -- NOTE: requires adjustment to be turned on
--   -- it should be marked as expandable
--   -- expected: two//| ?four
--   #eval unify_reduce_adj (empty.insert 7) 10
--   [lesstype| (one//unit -> two//unit) & (three//unit -> four//unit) ]
--   [lesstype| (one//unit | three//unit) -> {β[0] with β[0] <: α[7]} ]
--   [lesstype| α[7] ]


-- -----------------

--   #eval unify_simple 10
--   [lesstype| (one//unit -> two//unit)  ]
--   [lesstype| (one//unit | three//unit) -> {β[0]} ]

--   #eval unify_simple 10
--   [lesstype| (three//unit -> four//unit) ]
--   [lesstype| (one//unit | three//unit) -> {β[0]} ]


-- ---------------------------------------------------


--   -- expected: one//unit | three//unit
--   #eval unify_reduce 10
--   [lesstype| (one//unit -> two//unit) & (three//unit -> four//unit) ]
--   [lesstype| α[7] -> (two//unit | four//unit) ]
--   [lesstype| α[7] ]


--   -------------------------------------------
--   -- requires weakening of return type in app
--   -- expected: two//unit | four//unit
--   -- may be affected initial expected type in infer_reduce 
--   #eval infer_reduce 0 [lessterm|
--     let _ : one//unit | three//unit = _ in
--     (
--       (_ => match y[0] 
--         case one;; => two;; 
--         case three;; => four;;
--       )
--       (y[0])
--     )
--   ]

--   -- imprecise 
--   -- expected: one//unit
--   #eval infer_reduce 0 [lessterm|
--     let _ : one//unit | three//unit = _ in
--     (
--       (_ => match y[0] 
--         case one;; => y[0] 
--         case three;; => one;;
--       )
--       (y[0])
--     )
--   ]

--   ---------- implication intersection ---------
--   -- (S -> T1) & (S -> T2) <: (S -> T1 & T2)

--   -- expected: true
--   #eval unify_decide 10 
--   [lesstype| (one//unit -> two//unit) & (one//unit -> three//unit) ]
--   [lesstype| one//unit -> (two//unit & three//unit)]

--   ----------------------------------

--   -- NOTE: in right-existential: if key is not matchable; save the relation
--   -- expected: true 
--   #eval unify_decide 10 
--   [lesstype| succ//α[1] * α[0] ]
--   [lesstype| {(succ//β[0] * cons//β[1]) with (β[0] * β[1]) <: ⟨nat_list⟩ # 2} ]

--   ---------- relational propagation ---------

--   -- NOTE: these are all dependent on an antecedent existential rule

--   -- incomplete
--   -- NOTE: variables are no longer expanded; 
--   -- need a generalized disjunction elimination rule 
--   -- or some general elimination rule for intersection of implication; e.g a factoring rule.
--   -- expected thing//unit | other//unit
--   #eval unify_reduce 10 
--   [lesstype| (zero//unit -> thing//unit) & (succ//α[1] -> other//unit)]
--   [lesstype| {β[0] with β[0] * α[0] <: ⟨nat_list⟩} -> α[2]]
--   [lesstype| α[2] ]

--   -- incomplete
--   -- expected: other//unit | thing//unit 
--   #eval unify_reduce 10 
--   [lesstype| (succ//⟨nat_⟩ -> other//unit) & (zero//unit -> thing//unit)]
--   [lesstype| {β[0] with β[0] * α[0] <: ⟨nat_list⟩} -> α[2]]
--   [lesstype| α[2] ]

--   -- incomplete
--   -- expected: nil//unit | other//unit
--   #eval unify_reduce 10 
--   [lesstype| (zero//unit -> α[0]) & (succ//α[1] -> other//unit)]
--   [lesstype| {β[0] with β[0] * α[0] <: ⟨nat_list⟩} -> α[2]]
--   [lesstype| α[2] ]

--   -- incomplete
--   -- expected: nil//unit | other//unit
--   #eval unify_reduce 10 
--   [lesstype| (zero//unit -> α[0]) & (succ//⟨list_⟩ -> other//unit)]
--   [lesstype| {β[0] with β[0] * α[0] <: ⟨nat_list⟩} -> α[2]]
--   [lesstype| α[2] ]

--   -- incomplete
--   -- expected: nil//unit | other//unit
--   #eval infer_reduce 10 [lessterm|
--     let _ : α[0] = _ in
--     let _ : {β[0] with β[0] * α[0] <: ⟨nat_list⟩} = _ in
--     (
--       (_ => match y[0] 
--         case zero;; => y[1] 
--         case succ; y[0] => other;;
--       )
--       (y[0])
--     )
--   ]

--   ----- using function application --------

--   -- incomplete
--   -- NOTE: full reduction requires using unify_all to solve remaining constraints
--   -- NOTE: return type should not be refined further after return
--   -- expected: zero//unit | other//unit
--   #eval infer_reduce 10 [lessterm|
--     let _ : [_<:α[0]] β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} = _ in
--     let _ = _ in
--     (
--       (_ => match y[0] 
--         case nil;; => y[0] 
--         case cons;y[0] => other;;
--       )
--       (y[1](y[0]))
--     )
--   ]

--   -- argument type is weaker than parameter type
--   -- expected: none 
--   #eval infer_reduce 10 [lessterm|
--     let _ : α[0] = _ in
--     let _ : {β[0] with β[0] * α[0] <: ⟨nat_list⟩} = _ in
--     (
--       (_ => match y[0] 
--         case zero;; => y[1]
--       )
--       (y[0])
--     )
--   ]


--   -------- collapsing ------------

--   -- expected: multiple environments
--   #eval infer_simple 0 [lessterm| 
--     let _ = _ in 
--     (_ => match y[0] 
--       case one;; => two;; 
--       case three;; => four;;
--     )(y[0])
--   ]


--   -- expected: none 
--   #eval infer_reduce 0 [lessterm| 
--     let _ = _ in 
--     (_ => match y[0] 
--       case two;; => thing;;
--     ) 
--     ((_ => match y[0] 
--       case one;; => two;; 
--       case three;; => four;;)(y[0]))
--   ]

--   #eval infer_simple 0 [lessterm| 
--     let _ = _ in 
--     let _ = (_ => match y[0] 
--       case one;; => two;; 
--       case three;; => four;;
--     )(y[0]) in
--     y[0]
--   ]

--   -- sound because initial type may be restricted
--   -- there exists a type that can be inhabited 
--   -- expected: one//unit
--   #eval infer_reduce 0 [lessterm| 
--     let _ = _ in 
--     let _ = (_ => match y[0] case one;; => two;; case three;; => four;;)(y[0]) in
--     let _ = (_ => match y[0] case two;; => thing;;)(y[0]) in
--     y[2]
--   ]

--   -- expected: thing//unit
--   #eval infer_reduce 0 [lessterm| 
--     let _ = _ in 
--     let _ = (_ => match y[0] case one;; => two;;)(y[0]) in
--     (_ => match y[0] case two;; => thing;;)(y[0])
--   ]

--   --------------------------------------


--   -- expected: ((one//unit -> two//unit) & (three//unit -> four//unit))
--   #eval infer_reduce 0 [lessterm| 
--     (_ => match y[0] case one;; => two;; case three;; => four;;)
--   ]

--   -- imprecise: inferring union instead of intersection
--   -- requires generalization upon detection of funciton types
--   -- expected: ((one//unit -> two//unit) & (three//unit -> four//unit))
--   #eval infer_reduce 0 [lessterm| 
--     (_ => (_ => match y[0] case one;; => two;; case three;; => four;;)(y[0]))
--   ]

--   #eval infer_envs 0 [lessterm| 
--     (_ => (_ => match y[0] case one;; => two;; case three;; => four;;)(y[0]))
--   ]

--   #eval infer_reduce 0 [lessterm| 
--     let _ = _ in
--     (_ => match y[0] 
--       case one;; => two;; 
--       case three;; => four;;)(y[0])
--   ]

--   #eval unify_reduce 10
--   [lesstype| (one//unit -> two//unit) & (three//unit -> four//unit) ]
--   [lesstype| α[7] -> α[8]]
--   [lesstype| α[7] -> α[8]]

--   ------- path selection --------------
--   -- expected: two//unit 
--   #eval infer_reduce 0 [lessterm| 
--     (_ => match y[0] case one;; => two;; case three;; => four;;)(one;;) 
--   ]

-- ------------------------------

--   -- expected: false
--   #eval unify_decide 0
--   [lesstype| {β[0] with β[0] * cons//cons//nil//unit <: ⟨nat_list⟩}]
--   [lesstype| succ//foo//zero//unit ]

--   #eval unify_reduce 10
--   [lesstype| {β[0] with β[0] * cons//cons//nil//unit <: ⟨nat_list⟩}]
--   [lesstype| α[0]]
--   [lesstype| α[0]]

--   #eval unify_reduce 10
--   [lesstype| α[0] * cons//cons//nil//unit]
--   nat_list
--   [lesstype| α[0] ]

--   #eval unify_decide 10
--   [lesstype| succ//foo//zero//unit ]
--   [lesstype| succ//succ//zero//unit ]

--   --------- sound application --------

--   -- expected: false
--   #eval unify_decide 10
--   [lesstype|
--     {β[0] * β[1] with (x : β[0] & y : β[1] & z : succ//zero//unit ) <: ⟨plus⟩}
--   ]
--   [lesstype| (zero//unit * succ//zero//unit) ]

--   -- incomplete: not fully reduced
--   -- expected: ((zero//unit * succ//zero//unit) | (succ//zero//unit * zero//unit))
--   #eval unify_reduce 10
--   [lesstype|
--     {β[0] * β[1] with (x : β[0] & y : β[1] & z : succ//zero//unit ) <: ⟨plus⟩}
--   ]
--   [lesstype| α[7] ]
--   [lesstype| α[7] ]

--   #eval unify_reduce 10
--   [lesstype|
--     [_] β[0] -> {β[0] * β[1] with (x : β[0] & y : β[1] & z : β[2]) <: ⟨plus⟩}
--   ]
--   [lesstype| succ//zero//unit -> α[7] ]
--   [lesstype| α[7] ]

--   -- incomplete: not fully reduced
--   -- expected: ((zero//unit * succ//zero//unit) | (succ//zero//unit * zero//unit))
--   #eval infer_reduce 10
--   [lessterm|
--     let _ : [_] β[0] -> {β[0] * β[1] with (x : β[0] & y : β[1] & z : β[2]) <: ⟨plus⟩} =  _ in
--     y[0](succ;zero;;)
--   ]
--   -----------------------------------

--   -- expected: none 
--   #eval unify_reduce 10
--   [lesstype|
--     (zero//unit * succ//zero//unit) -> unit
--   ]
--   [lesstype| ((zero//unit * succ//zero//unit) | (succ//zero//unit * zero//unit)) -> α[7] ]
--   [lesstype| α[7] ]

--   -- expected: none 
--   #eval infer_reduce 10
--   [lessterm|
--     let _ : [_] β[0] -> {β[0] * β[1] with (x : β[0] & y : β[1] & z : β[2]) <: ⟨plus⟩} =  _ in
--     let _ : (zero//unit * succ//zero//unit) -> unit = _ in 
--     y[0](y[1](succ;zero;;))
--   ]

--   -- expected: unit
--   #eval infer_reduce 10
--   [lessterm|
--     let _ : (foo//unit) -> unit = _ in 
--     y[0](foo;;)
--   ]

--   -- expected: none 
--   #eval infer_reduce 10
--   [lessterm|
--     let _ : (foo//unit) -> unit = _ in 
--     y[0](boo;;)
--   ]

--   -------------------------------------------
--   ---------- let binding soundness -----------

--   -- expected: none 
--   #eval infer_reduce 10
--   [lessterm|
--     let _ : [_] β[0] -> {β[0] * β[1] with (x : β[0] & y : β[1] & z : β[2]) <: ⟨plus⟩} =  _ in
--     let _ : (zero//unit * succ//zero//unit) = y[0](succ;zero;;) in
--     y[0]

--   ]

--   ----------- left-inductive -----------------

--   -- expected: true
--   #eval unify_decide 30
--   [lesstype| ⟨nat_⟩ ] 
--   [lesstype| (zero//unit | succ//⟨nat_⟩) ]

--   -- expected: true
--   #eval unify_decide 30
--   [lesstype| ((zero//unit | succ//⟨nat_⟩)) ] 
--   [lesstype| (⟨nat_⟩) ]

--   -- expected: true 
--   #eval unify_decide 0
--   [lesstype| ⟨nat_list⟩ ]
--   [lesstype| ⟨nat_⟩ * ⟨list_⟩ ]

--   -- NOTE: this requires factoring to circumvent circular variable restriction.
--   #eval unify_decide 10
--   [lesstype| ⟨nat_list⟩ ]
--   [lesstype| ⟨nat_⟩ * α[1] ]


--   ------- specialization --------------
--   -- NOTE: this is specialized because left-universal checks constraints after unification
--   -- expected: even 
--   #eval infer_reduce 0 [lessterm|
--   let _ : [_<:⟨nat_⟩] β[0] * β[0] -> β[0] = _ in 
--   let _ : ⟨even⟩ = _ in
--   (y[1] (y[0], zero;;))
--   ]

--   -- expected: nat 
--   #eval infer_reduce 0 [lessterm|
--   let _ : [_<:⟨nat_⟩] β[0] * β[0] -> β[0] = _ in 
--   let _ : ⟨even⟩ = _ in
--   (y[1] (zero;;, y[0]))
--   ]



-- --------------------------------------

-- -----------------------------------
-- -- uninhabitable
-- -----------------------------------

--   -- is unification with uninhabitable types unsound?
--   -- assigment indicates a subtyping; (not a typing)
--   -- the existience of a subtyping does not imply the existence of a typing; 
--   -- that is, the subtype could also be empty 
--   -- thus it does not introduce a false premise in order to draw a false conclusion

--   -- α[7] is an uninhabitable type
--   #eval unify_decide 10 
--   [lesstype| α[7] ]
--   [lesstype| {β[0] with succ//β[0] <: foo//β[0]} ]

--   -- α[0] is an uninhabitable type
--   #eval unify_decide 30
--   [lesstype| [_<:top] β[0] -> {β[0] with β[1] * β[0] <: ⟨nat_list⟩} ]
--   [lesstype| foo//succ//zero//unit -> α[0] ] 

--   -- expected false
--   #eval unify_decide 30
--   [lesstype| [_<:{β[1] -> β[0] with β[1] * β[0] <: ⟨nat_list⟩}] β[0] ]
--   [lesstype| foo//succ//zero//unit -> α[0] ] 


-- -------------------------------------
--   -- max example 
-- -------------------------------------


--   -- incomplete
--   -- expected: notions of zero//and true//appear in inferred type
--   -- this requires including relational constraints in generalization
--   #eval infer_reduce 0 [lessterm| 
--     (_ => (fix (_ => _ => match y[0]
--       case (zero;;, zero;;) => true;;  
--     )) (y[0]))
--   ] 

--   -- incomplete: lack of recursive call causes failure
--   #eval infer_reduce 0 [lessterm| 
--     (fix (_ => _ => match y[0]
--       case (zero;;, zero;;) => true;;
--     ))
--   ] 

--   #eval infer_reduce 0 [lessterm| 
--     (fix (_ => _ => match y[0]
--       case (zero;;, zero;;) => y[0](true;;)
--     ))
--   ] 

--   -- incomplete
--   -- expected: true//unit
--   #eval infer_reduce 0 [lessterm| 
--     let _ = (_ => ((fix (_ => _ => match y[0]
--       case (zero;;, zero;;) => true;;  
--     )) (y[0])))
--     in
--     (y[0] (zero;;, zero;;))
--   ] 

--   def nat_pair := [lesstype|
--     induct
--       {(zero//unit * ⟨nat_⟩)} 
--       | 
--       {(succ//β[0] * succ//β[1]) with (β[0] * β[1]) <: β[2] } 
--       | 
--       {(succ//⟨nat_⟩ * zero//unit)}
--   ]

--   -- expected: relational function type
--   #eval infer_reduce 0 [lessterm| 
--     fix (_ => _ => match y[0]
--       case (zero;;, y[0]) => true;;  
--       case (succ; y[0], succ; y[1]) => (y[3] (y[0], y[1])) 
--       case (succ; y[0], zero;;) => false;; 
--     )
--   ] 
    
--   -- expected: false//unit
--   #eval infer_reduce 0 [lessterm| 
--     -- less than or equal:
--     let _ = fix (_ => _ => match y[0]
--       case (zero;;, y[0]) => true;;  
--       case (succ; y[0], succ; y[1]) => (y[3] (y[0], y[1])) 
--       case (succ; y[0], zero;;) => false;; 
--     ) in
--     (
--       (_ => y[0])
--       (y[0] (succ; succ; zero;;, succ; zero;;))
--     )
--   ] 

--   -- expected: the argument type should be refined by the function application 
--   #eval infer_reduce 0 [lessterm| 
--     -- less than or equal:
--     let _ = fix (_ => _ => match y[0]
--       case (zero;;, y[0]) => true;;  
--       case (succ; y[0], succ; y[1]) => (y[2] (y[0], y[1])) 
--       case (succ; y[0], zero;;) => false;; 
--     ) in
--     (_ => match y[0] case (y[0], y[1]) => 
--       (
--         let _ = (y[3] (y[0], y[1])) in
--         y[1]
--       )
--     )
--   ] 

--   -- expected: type maintains relational information 
--   #eval infer_reduce 0 [lessterm| 
--     let _ = fix (_ => _ => match y[0]
--       case (zero;;, y[0]) => true;;  
--       case (succ; y[0], succ; y[1]) => (y[3] (y[0], y[1])) 
--       case (succ; y[0], zero;;) => false;; 
--     ) in
--     let _ = (_ => match y[0] case (y[0], y[1]) => 
--         (y[3] (y[0], y[1]))
--     ) in
--     y[0]
--   ] 


--   -- NOTE: not reducible 
--   -- expected: none 
--   #eval unify_reduce 10
--   [lesstype| (α[1] * α[2]) * true//unit ]
--   [lesstype|
--   induct (
--       {((zero//unit * β[0]) * true//unit) # 1} |
--       {((succ//β[0] * succ//β[1]) * β[2]) with ((β[0] * β[1]) * β[2]) <: β[3] # 3} |
--       {((succ//β[0] * zero//unit) * false//unit) # 1}
--   )
--   ]
--   [lesstype| (α[1] * α[2]) * true//unit ]

--   -- expected: ?? 
--   #eval unify_decide 0
--   [lesstype|
--     ({β[0] with ((α[20] * α[18]) * β[0]) <: 
--       (induct ({((zero//unit * β[0]) * true//unit) # 1} |
--       ({((succ//β[1] * succ//β[2]) * β[0]) with ((β[1] * β[2]) * β[0]) <: β[3] # 3} |
--       {((succ//β[0] * zero//unit) * false//unit) # 1}))) # 1}
--   )
--   ]
--   [lesstype| true//unit ]


--   -- expected: type is maintained after identity function application
--   #eval infer_reduce 0 [lessterm| 
--     -- less than or equal:
--     let _ = fix (_ => _ => match y[0]
--       case (zero;;, y[0]) => true;;  
--       case (succ;y[0], succ; y[1]) => y[3](y[0], y[1])
--       case (succ;y[0], zero;;) => false;; 
--     ) in
--     (_ => match y[0] case (y[0], y[1]) => 
--       (
--         (_ => y[0])
--         (y[2] (y[0], y[1]))
--       )
--     )
--   ]

--   -- expected: type that describes max invariant
--   -- e.g. X -> Y -> {Z with (X * Z) <: LE, (Y * Z) <: LE}
--   #eval infer_reduce 0 [lessterm| 
--     let _ = fix (_ => _ => match y[0]
--       case (zero;;, y[0]) => true;;  
--       case (succ; y[0], succ; y[1]) => (y[3] (y[0], y[1])) 
--       case (succ; y[0], zero;;) => false;; 
--     ) in
--     let _ = _ in
--     let _ = _ in
--     (
--       if (y[2] (y[0], y[1])) then
--         y[1]
--       else
--         y[0]
--     )
--   ] 



--   -- expected: 
--   /-
--   (? >> (? >> ({2 // (β[1] * β[0]) with (β[1] * β[0]) <: (induct ({1 // (zero//unit * β[0])} |
--         ({3 // (succ//β[1] * succ//β[2]) with (β[1] * β[2]) <: β[3]} | {1 // (succ//β[0] * zero//unit)})))} >> β[0])))
--   -/
--   #eval unify_reduce 10 
--   [lesstype| 
--   α[0] * α[1]
--   ]
--   [lesstype| 
--   (induct (
--     {(zero//unit * β[0]) # 1} | 
--     {(succ//β[1] * succ//β[2]) with (β[1] * β[2]) <: β[3] # 3} |
--     {(succ//β[0] * zero//unit) # 1}
--   )) 
--   ]
--   [lesstype| 
--   α[0] * α[1]
--   ]

--   -- expected: 
--   /-
--   (? >> (? >> ({2 // (β[1] * β[0]) with (β[1] * β[0]) <: (induct ({1 // (zero//unit * β[0])} |
--         ({3 // (succ//β[1] * succ//β[2]) with (β[1] * β[2]) <: β[3]} | {1 // (succ//β[0] * zero//unit)})))} >> β[0])))
--   -/
--   #eval unify_reduce 10 
--   [lesstype| 
--   [_<:(induct (
--     {(zero//unit * β[0]) # 1} | 
--     {(succ//β[1] * succ//β[2]) with (β[1] * β[2]) <: β[3] # 3} |
--     {(succ//β[0] * zero//unit) # 1}
--   ))] (β[0] ->
--     {β[0] with (β[1] * β[0]) <: (induct 
--       {((zero//unit * β[0]) * true//unit) # 1} |
--       {((succ//β[1] * succ//β[2]) * β[0]) with ((β[1] * β[2]) * β[0]) <: β[3] # 3} |
--       {((succ//β[0] * zero//unit) * false//unit) # 1}
--     ) # 1}
--   )
--     ]
--   [lesstype| 
--   α[0] * α[1] -> α[2]
--   ]
--   [lesstype| 
--   α[0] * α[1]
--   ]

--   #eval unify_reduce 10 
--   [lesstype| α[0] * α[1] ]
--   nat_list
--   [lesstype| α[0] * α[1] ]

--   -- NOTE: unify_all breaks this
--   -- complete
--   -- expected: type that describes max invariant
--   -- e.g. X -> Y -> {Z with (X * Z) <: LE, (Y * Z) <: LE}
--   #eval infer_reduce 0 [lessterm| 
--     let _ = fix (_ => _ => match y[0]
--       case (zero;;, y[0]) => true;;  
--       case (succ; y[0], succ; y[1]) => (y[3] (y[0], y[1])) 
--       case (succ; y[0], zero;;) => false;; 
--     ) in
--     (_ => match y[0] case (y[0], y[1]) => 
--       (
--         if (y[3] (y[0], y[1])) then
--           y[1]
--         else 
--           y[0]
--       )
--     ) 
--   ] 

-- /-
-- {2 # ((β[0] * β[1]) -> β[1]) with ((β[0] * β[1]) * true//unit) <: (induct (
--       ((zero//unit * α[7]) * true//unit) |
--       {3 # ((succ//β[1] * succ//β[2]) * β[0]) with ((β[1] * β[2]) * β[0]) <: β[3]} |
--       ((succ//α[14] * zero//unit) * false//unit)
-- ))} |

-- {2 # ((β[0] * β[1]) -> β[0]) with ((β[0] * β[1]) * false//unit) <: (induct (
--       ((zero//unit * α[7]) * true//unit) |
--       {3 # ((succ//β[1] * succ//β[2]) * β[0]) with ((β[1] * β[2]) * β[0]) <: β[3]} |
--       ((succ//α[14] * zero//unit) * false//unit)
-- ))}
-- -/

--   -- complete
--   -- NOTE: max of the two inputs  
--   -- expected: succ//succ//succ//zero//unit   
--   #eval infer_reduce 0 [lessterm| 
--     let _ = fix (_ => _ => match y[0]
--       case (zero;;, y[0]) => true;;  
--       case (succ; y[0], succ; y[1]) => (y[3] (y[0], y[1])) 
--       case (succ; y[0], zero;;) => false;; 
--     ) in
--     let _ = (_ => match y[0] case (y[0], y[1]) =>
--       (
--         if (y[3] (y[0], y[1])) then
--           y[1]
--         else
--           y[0]
--       )
--     ) in
--     (y[0] (succ;zero;;, succ;succ;succ;zero;;))
--   ] 


--   -- incomplete 
--   -- actual: {X with X > 1} 
--   -- expected: succ//succ//succ//zero//unit   
--   #eval infer_reduce 0 [lessterm| 
--     let _ = fix (_ => _ => match y[0]
--       case (zero;;, y[0]) => true;;  
--       case (succ; y[0], succ; y[1]) => (y[3] (y[0], y[1])) 
--       case (succ; y[0], zero;;) => false;; 
--     ) in
--     let _ = (_ => match y[0] case (y[0], y[1]) =>
--       (
--         if (y[3] (y[0], y[1])) then
--           y[1]
--         else
--           y[0]
--       )
--     ) in
--     (y[0] (succ;succ;succ;zero;;, succ;zero;;))
--   ] 

--   -- complete
--   -- NOTE: merely require some of the function paths to match
--   -- not necessary for all cases to succeed
--   -- expected: succ//succ//succ//zero//unit   
--   #eval infer_reduce 0 [lessterm| 
--     (_ => match y[0] case (y[0], y[1]) => 
--       (
--         if 
--           (fix(_ => _ => match y[0]
--             case (zero;;, y[0]) => true;;  
--             case (succ; y[0], succ; y[1]) => (y[2] (y[0], y[1])) 
--             case (succ; y[0], zero;;) => false;; 
--           ) (y[0], y[1]))
--         then
--           y[1]
--         else
--           y[0]
--       )
--     ) 
--     ((succ; zero;;, succ; succ; succ; zero;;))
--   ] 


--   def led_ := [lesstype|
--     induct 
--       {((zero//unit * β[0]) * true//unit) # 1} |
--       {((succ//β[1] * succ//β[2]) * β[0]) with ((β[1] * β[2]) * β[0]) <: β[3] # 3} |
--       {((succ//β[0] * zero//unit) * false//unit) # 1}
--   ]

--   -------------
--   #eval unify_reduce 10
--   [lesstype|
--     (([_<:{((β[0] * β[1]) -> β[1]) with ((β[0] * β[1]) * true//unit) <: ⟨led_⟩ # 2}] β[0])) & 
--     (([_<:{((β[0] * β[1]) -> β[0]) with ((β[0] * β[1]) * false//unit) <: ⟨led_⟩ # 2}] β[0]))
--   ]
--   [lesstype| succ//zero//unit * succ//succ//succ//zero//unit -> α[7] ]
--   [lesstype| α[7]]


--   -- expected: succ//succ//succ//zero//unit
--   #eval unify_reduce 10
--   [lesstype| (succ//zero//unit * succ//succ//succ//zero//unit) * α[7] ]
--   [lesstype|
--     ({((β[0] * β[1]) * β[1]) with ((β[0] * β[1]) * true//unit) <: ⟨led_⟩ # 2}) 
--     |
--     ({((β[0] * β[1]) * β[0]) with ((β[0] * β[1]) * false//unit) <: ⟨led_⟩ # 2})
--   ]
--   [lesstype| α[7]]

--   -- expected: succ//succ//succ//zero//unit
--   #eval unify_reduce 10
--   [lesstype| (succ//succ//succ//zero//unit * succ//zero//unit) * α[7] ]
--   [lesstype|
--     ({((β[0] * β[1]) * β[1]) with ((β[0] * β[1]) * true//unit) <: ⟨led_⟩ # 2}) 
--     |
--     ({((β[0] * β[1]) * β[0]) with ((β[0] * β[1]) * false//unit) <: ⟨led_⟩ # 2})
--   ]
--   [lesstype| α[7]]

--   --------------- debugging ---------------

--   -- complete
--   -- expected: false//unit 
--   #eval infer_reduce 0 [lessterm| 
--     (
--       (fix (_ => _ => match y[0]
--         case (zero;;, y[0]) => true;;  
--         case (succ; y[0], succ; y[1]) => (y[3] (y[0], y[1])) 
--         case (succ; y[0], zero;;) => false;; 
--       ))
--       (succ; succ; zero;;, succ; zero;;)
--     )
--   ] 

--   #eval infer_reduce 0 [lessterm| 
--     let _ = (fix (_ => _ => match y[0]
--       case (zero;;, y[0]) => true;;  
--       case (succ; y[0], succ; y[1]) => (y[3] (y[0], y[1])) 
--       case (succ; y[0], zero;;) => false;; 
--     )) in
--     (y[0] (succ; succ; zero;;, succ; zero;;))
--   ] 

--   #eval infer_reduce 0 [lessterm| 
--     (fix (_ => _ => match y[0]
--       case (zero;;, y[0]) => true;;  
--       case (succ; y[0], succ; y[1]) => (y[2] (y[0], y[1])) 
--       case (succ; y[0], zero;;) => false;; 
--     ))
--   ] 



--   #eval unify_decide 10 
--   [lesstype| succ//zero//unit * zero//unit]
--   nat_pair


--   def le_ := [lesstype|
--     induct
--       {(zero//unit * β[0]) * true//unit} 
--       | 
--       {(succ//β[0] * succ//β[1]) * β[2] with (β[0] * β[1]) * β[2] <: β[3] } 
--       | 
--       {(succ//β[0] * zero//unit) * false//unit}
--   ]

--   -- expected: none 
--   #eval unify_reduce 10 
--   [lesstype|
--     ([_<:ooga//unit]
--        (β[0] -> {β[0] with (β[1] * β[0]) <: ⟨le_⟩ # 1}))
--   ]
--   [lesstype| succ//succ//zero//unit * succ//zero//unit -> α[0]]
--   [lesstype| α[0] ]

--   -- incomplete: not reducing all the way
--   -- expected: false//unit 
--   #eval unify_reduce 10 
--   [lesstype| ([_<:⟨nat_pair⟩] (β[0] -> {β[0] with (β[1] * β[0]) <: ⟨le_⟩ # 1})) ]
--   [lesstype| succ//succ//zero//unit * succ//zero//unit -> α[0]]
--   [lesstype| α[0] ]

-- -------------------------------------
--   -- sum example 
-- -------------------------------------

--   def diff := [lessterm|
--     fix(_ => _ => match y[0] 
--       case (succ; y[0], succ; y[1]) => (y[3] (y[0], y[1]))
--       case (zero;;, y[0]) => y[0]
--       case (y[0], zero;;) => y[0] 
--     )
--   ]

--   #eval infer_reduce 10  [lessterm|
--     let _ = ⟨diff⟩ in
--     (y[0] (succ; succ; zero;;, succ; zero;;))
--   ]


--   def leq := [lessterm|
--     fix (_ => _ => match y[0]
--       case (zero;;, y[0]) => true;;  
--       case (succ; y[0], succ; y[1]) => (y[3] (y[0], y[1])) 
--       case (succ; y[0], zero;;) => false;; 
--     )
--   ]

--   def max := [lessterm| 
--     (_ => match y[0] case (y[0], y[1]) => 
--       (
--         if (⟨leq⟩ (y[0], y[1])) then
--           y[1]
--         else
--           y[0]
--       )
--     ) 
--   ] 

--   def add := [lessterm|
--     fix(_ => _ => match y[0] 
--       case (zero;;, y[0]) => y[0] 
--       case (succ; y[0], y[1]) => succ; (y[3] (y[0], y[1]))
--     )
--   ]

--   #eval infer_reduce 0 add 

--   def sum := [lessterm|
--     fix(_ => _ => match y[0]
--       case zero;; => zero;; 
--       case succ; y[0] => (
--         (⟨add⟩)((y[2](y[0]), succ;y[0]))
--       )
--     )
--   ]

--   --expected: type that relates the recursive result type variable to the application's result type 
--   /-
--        {2 // (succ//X * A) with (X, Y) <: self} 
--        where
--         add (e1, e2) : A 
--         e1 : Y
--         e2 : succ//X 
--   -/
--   #eval infer_reduce 0 sum 

--   #eval infer_reduce 0 [lessterm| 
--     (⟨sum⟩)(succ;succ;zero;;) 
--   ]

--   -- sum(2) : {v | v >= 2} 
--   -- 0 : {v | v >= 2} 
--   -- expected: false 
--   #eval match (infer_reduce 0 [lessterm| ⟨sum⟩(succ;succ;zero;;)]) with
--   | some ty => unify_decide 0 [lesstype| zero//unit ] ty
--   | none => false

--   -- sum(2) : {v | v >= 2} 
--   -- 1 : {v | v >= 2} 
--   -- expected: false 
--   #eval match (infer_reduce 0 [lessterm| ⟨sum⟩(succ;succ;zero;;)]) with
--   | some ty => unify_decide 0 [lesstype| succ//zero//unit ] ty
--   | none => false

--   -- sum(2) : {v | v >= 2} 
--   -- 2 : {v | v >= 2} 
--   -- expected: true
--   #eval match (infer_reduce 0 [lessterm| ⟨sum⟩(succ;succ;zero;;)]) with
--   | some ty => unify_decide 0 [lesstype| succ//succ//zero//unit ] ty
--   | none => false

--   -- sum(2) : {v | v >= 2} 
--   -- 3 : {v | v >= 2} 
--   -- expected: true 
--   #eval match (infer_reduce 0 [lessterm| ⟨sum⟩(succ;succ;zero;;)]) with
--   | some ty => unify_decide 0 [lesstype| succ//succ//succ//zero//unit ] ty
--   | none => false


--   #eval infer_reduce 0 [lessterm| 
--     (⟨sum⟩)(succ;zero;;) 
--   ]

--   -- expected: false 
--   #eval match (infer_reduce 0 [lessterm| ⟨sum⟩(succ;zero;;)]) with
--   | some ty => unify_decide 0 [lesstype| zero//unit ] ty
--   | none => false

--   -- expected: true
--   #eval match (infer_reduce 0 [lessterm| ⟨sum⟩(succ;zero;;)]) with
--   | some ty => unify_decide 0 [lesstype| succ//zero//unit ] ty
--   | none => false


--   #eval infer_reduce 0 [lessterm| 
--     (⟨sum⟩)(zero;;) 
--   ]

--   -- expected: true 
--   #eval match (infer_reduce 0 [lessterm| ⟨sum⟩(zero;;)]) with
--   | some ty => unify_decide 0 [lesstype| zero//unit ] ty
--   | none => false

--   -------------------------------------
--   /-
--   foldn example 
--   -/
--   -------------------------------------

--   def lt := [lessterm|
--     fix (_ => _ => match y[0]
--       case (zero;;, succ;zero;;) => true;;  
--       case (succ; y[0], succ; y[1]) => (y[3] (y[0], y[1])) 
--       case (y[0], zero;;) => false;; 
--     )
--   ]

--   #eval infer_reduce 0 lt

--   -- expected: true//unit
--   #eval infer_reduce 0 [lessterm| 
--     ⟨lt⟩(zero;;, succ;zero;;) 
--   ]

--   -- expected: true//unit
--   #eval infer_reduce 0 [lessterm| 
--     ⟨lt⟩(succ;zero;;, succ;succ;zero;;) 
--   ]

--   -- expected: false//unit
--   #eval infer_reduce 0 [lessterm| 
--     ⟨lt⟩(zero;;, zero;;) 
--   ]

--   -- expected: false//unit
--   #eval infer_reduce 0 [lessterm| 
--     ⟨lt⟩(succ;zero;;, succ;zero;;) 
--   ]

--   -- expected: false//unit
--   #eval infer_reduce 0 [lessterm| 
--     ⟨lt⟩(succ;succ;zero;;, succ;zero;;) 
--   ]

--   #eval infer_reduce 0 [lessterm| 
--     ⟨lt⟩ 
--   ]

-- ---------------
--   def foldn := [lessterm|
--   let _ = _ in
--   let _ = _ in
--   _ => match y[0] case (y[0], (y[1], y[2])) => (
--       let _ = fix(_ => _ => match y[0] case (y[0], y[1]) =>
--         /-
--         n, b, f: 4, 5, 6 
--         loop: 3 
--         i, c: 0, 1 
--         -/
--         (if ⟨lt⟩(y[0], y[4]) then
--           -- y[3](succ;y[0], y[6](y[0], y[1]))
--           y[3](succ;y[0], ;)
--         else
--           y[1]
--         )
--       ) in 
--       /-
--       loop: 0 
--       n: 1
--       b: 2
--       f: 3
--       -/
--       y[0](zero;;, y[2])
--       -- y[0]
--   )
--   ]

--   /-
--   incomplete
--   ERROR: naive decreasing requirement for unifying with inductive type is overly strict  
--   TODO: convert to leverging CHC solver, and rely on external decidability heuristics 
--   -/
--   #eval infer_reduce 0 foldn

--   /-
--   ERROR: fails due to overly strict and naive decreasing heuristic
--   -/ 
--   #eval decreasing 0
--   [lesstype|
--     -- THE succ//β[1] is not decreasing!!
--     {((β[1] * β[2]) * β[0]) with ((succ//β[1] * unit) * β[0]) <: β[3] # 3}
--   ]

--   -------------------------------
--   /-
--   pattern matching type inference 
--   -/
--   -------------------------------
--   /-
--   Pattern matching should include switch, rather then merely having branches of a function.
--   Inclusion of switch allows more precise typing; since switch <: pattern constraint can be leveraged for inferring type for each case.
--   Seems related to occurence typing
--   -/
--   #eval infer_reduce 0 [lessterm|
--     let _ = _ in
--     (_ => match y[0]
--       case XO;; => (_ => match y[0] case XO;; => XX;;)(y[0]) -- need to prevent this assignment from escaping
--       case YO;; => YY;;
--     )
--   ]

--   #eval infer_reduce 0 [lessterm|
--     (_ => 
--       (_ => match y[0]
--         case XO;; => (_ => match y[0] case XO;; => XX;;)(y[0]) -- need to prevent this assignment from escaping
--         case YO;; => YY;;
--       )((y[0]))
--     )
--   ]

-- ----------------------------------

--   def zero := [lessterm|
--     _ => match y[0]
--     case zero;; => true;;  
--     case succ;y[0] => false;; 
--   ]

--   #eval infer_reduce 0 [lessterm|
--     fix(_ => _ =>
--       if ⟨zero⟩(y[0]) then
--         zero;;
--       else
--         match y[0] 
--         case succ;y[0] => succ;(y[2](y[0]))
--     )(succ;zero;;)
--   ]

--   #eval infer_reduce 0 [lessterm|
--     fix(_ => _ => match y[0]
--       case zero;; => zero;; 
--       case succ;y[0] => succ;y[2](y[0])
--     )(succ;zero;;)
--   ]

end Nameless 