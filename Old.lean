
  --   inductive Combo (α : Type)
  --   | bvar : Nat -> Combo α  
  --   | fvar : Nat -> Combo α
  --   | unit : Combo α
  --   | top : Combo α 
  --   | bot : Combo α
  --   | tag : String -> α -> Combo α
  --   | field : String -> α -> Combo α
  --   | union : α -> α -> Combo α
  --   | inter : α -> α -> Combo α
  --   | case : α -> α -> Combo α
  --   | exis : Nat -> α -> α -> α -> Combo α
  --   | univ : Nat -> α -> α -> α -> Combo α
  --   | recur : α -> Combo α
  --   deriving Repr, Inhabited, Hashable, BEq


  --   def traverse (f : Combo α -> α): Ty ->  α
  --   | bvar id => f (.bvar id)  
  --   | fvar id => f (.fvar id)
  --   | unit => f .unit 
  --   | top => f .top 
  --   | bot => f .bot 
  --   | tag label content => f (.tag label (traverse f content))
  --   | field label content => f (.field label (traverse f content))
  --   | union ty1 ty2 => f (.union (traverse f ty1) (traverse f ty2))
  --   | inter ty1 ty2 => f (.inter (traverse f ty1) (traverse f ty2))
  --   | case ty1 ty2 => f (.case (traverse f ty1) (traverse f ty2))
  --   | exis n ty_c1 ty_c2 ty_pl => f (.exis n (traverse f ty_c1) (traverse f ty_c2) (traverse f ty_pl))
  --   | univ n ty_c1 ty_c2 ty_pl => f (.univ n (traverse f ty_c1) (traverse f ty_c2) (traverse f ty_pl))
  --   | recur ty => f (.recur (traverse f ty))


    -- def wellformed (upper : Nat):  Ty -> Bool
    -- | .bvar id => (id < upper)
    -- | .fvar _ => true 
    -- | .unit => true 
    -- | .top => true 
    -- | .bot => true 
    -- | .tag _ content => wellformed upper content 
    -- | .field _ content => wellformed upper content 
    -- | .union ty1 ty2 => 
    --   wellformed upper ty1 && wellformed upper ty2 
    -- | .inter ty1 ty2 => 
    --   wellformed upper ty1 && wellformed upper ty2 
    -- | .case ty1 ty2 => 
    --   wellformed upper ty1 && wellformed upper ty2 
    -- | .exis n ty_c1 ty_c2 ty_pl => 
    --   wellformed (upper + n) ty_c1 && 
    --   wellformed (upper + n) ty_c2 &&
    --   wellformed (upper + n) ty_pl 
    -- | .univ n ty_c1 ty_c2 ty_pl => 
    --   wellformed (upper + n) ty_c1 && 
    --   wellformed (upper + n) ty_c2 &&
    --   wellformed (upper + n) ty_pl 
    -- | .recur ty => wellformed (upper + 1) ty 

    -- def signed_free_vars (posi : Bool) : Ty -> PHashMap Nat Unit
    -- | .bvar id => {} 
    -- | .fvar id => 
    --   if posi then
    --     let u : Unit := Unit.unit
    --     PHashMap.from_list [(id, u)] 
    --   else
    --     {}
    -- | .unit => {} 
    -- | .top => {} 
    -- | .bot => {} 
    -- | .tag l ty => (signed_free_vars posi ty) 
    -- | .field l ty => (signed_free_vars posi ty)
    -- | .union ty1 ty2 => signed_free_vars posi ty1 ; signed_free_vars posi ty2
    -- | .inter ty1 ty2 => signed_free_vars posi ty1 ; signed_free_vars posi ty2
    -- | .case ty1 ty2 => (signed_free_vars (!posi) ty1) ; signed_free_vars posi ty2
    -- | .exis n ty_c1 ty_c2 ty =>
    --   (signed_free_vars posi ty)
    -- | .univ n ty_c1 ty_c2 ty =>
    --   (signed_free_vars posi ty)
    -- | .recur ty => (signed_free_vars posi ty)


    -- def split_unions : Ty -> List Ty 
    -- | Ty.union ty1 ty2 =>
    --   (split_unions ty1) ++ (split_unions ty2)
    -- | ty => [ty]

    -- def extract_field (label : String) (ty : Ty) : Option Ty := do
    --   let fields <- (linearize_fields ty)
    --   let fields_filt := fields.filter (fun (l, _) => l == label)
    --   if h : fields_filt.length > 0 then
    --     let (_, ty_fd) := (fields_filt.get ⟨0, h⟩)
    --     some ty_fd
    --   else
    --     none

    -- def extract_field_induct (label : String): Ty -> Option Ty 
    -- | .exis n ty (.bvar id) ty_pl => 
    --   -- assume β[n] is the inductive fixed point 
    --   if id == n then
    --     Option.bind (extract_field label ty) (fun ty => 
    --     Option.bind (extract_field label ty_pl) (fun ty_pl =>
    --       (Ty.exis n  ty (.bvar id) ty_pl)
    --     ))
    --   else 
    --     none
    -- | ty => extract_field label ty 

    -- -- from induction over union of intersections to intersection of induction over union
    -- partial def transpose_relation (labels : List String) : Ty -> Ty
    -- | Ty.recur ty =>
    --   let unions := split_unions ty
    --   labels.foldr (fun label ty_acc =>
    --     let ty_col := unions.foldr (fun ty_row ty_col =>
    --       match extract_field_induct label ty_row with
    --       | some ty_field => Ty.union ty_field ty_col 
    --       | none => Ty.top
    --     ) Ty.bot 
    --     Ty.inter (Ty.field label (Ty.recur ty_col)) ty_acc 
    --   ) Ty.top
    -- | ty => 
    --   Ty.top




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

    --   let ((i, contexts), env_relational) := ( 
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
    --         ((i, [env_ty]), env_relational.insert (.up, ty_norm) ty_c1)

    --       else ((i, []), env_relational) 
    --     | none => (unify i (env_ty) env_relational {} ty_c1 ty_c2, env_relational)
    --   )

    --   -- vacuous truth unsafe: given P |- Q, if P is incorreclty false, then P |- Q is incorrecly true (which is unsound)
    --   bind_nl (i, contexts) (fun i env_ty => 
    --   bind_nl (unify i env_ty env_relational {} ty1 ty2) (fun i env_ty => 
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
    --     bind_nl (unify i env_ty env_relational {} ty3 ty1) (fun i env_ty =>
    --       (unify i env_ty env_relational {} ty2 ty4)
    --     ) 
    --   else if n1 >= n3 then
    --     let (i, ids1) := (i + n1, (List.range n1).map (fun j => i + j))
    --     let args1 := ids1.map (fun id => Ty.fvar id)
    --     let ty1' := Ty.instantiate 0 args1 ty1
    --     let ty2' := Ty.instantiate 0 args1 ty2

    --     let (i, ids3) := (i + n3, (List.range n3).map (fun j => i + j))
    --     let is_introduction := fun key => ids3.contains key 
    --     let args3 := ids3.map (fun id => Ty.fvar id)
    --     let ty3' := Ty.instantiate 0 args3 ty3
    --     let ty4' := Ty.instantiate 0 args3 ty4

    --     bind_nl (unify i env_ty env_relational {} ty3' ty1') (fun i env_ty =>
    --       let is_result_safe := List.all env_ty.toList (fun (key, ty_value) =>
    --         not (is_introduction key)
    --       )
    --       if is_result_safe then
    --         (unify i env_ty env_relational {} ty2' ty4')
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

