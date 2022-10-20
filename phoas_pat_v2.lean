#eval Lean.versionString



@[reducible] def TupleN (α : Type) : Nat -> Type
  | 0 => Unit 
  | n + 1 => α × (TupleN α n)  

#check ((1, 2, ()) : TupleN Nat 2)
#check ((2, ()))


inductive Pat : (α : Type) -> Nat -> Type where
  | var : (x : α) -> Pat α 1
  | hole : Pat α 0 



mutual
  inductive Case (α : Type) : Nat -> Type
  | mk {n : Nat} : (Pat α n) -> (TupleN α n -> Tm α) -> Case α n

  inductive Tm (α : Type): Type
  | hole : Tm α 
  | var : α -> Tm α 
  | abs : (Σ n, Case α n) -> Tm α
  | app : Tm α -> Tm α -> Tm α
end


def Pat.to_string {n : Nat} (t : Pat String n) := match t with
  | Pat.var x => s!"{x}" 
  | Pat.hole => s!"_" 


def Pat.fresh {α β : Type} (i : Nat) (f : Nat -> β) {n : Nat}  : (Pat α n) -> 
  (TupleN β n) × (Pat β n) × Nat 
  | Pat.var _ => ((f i, ()), (Pat.var (f i)), i + 1)
  | Pat.hole => ((), (Pat.hole), i)

def Pat.fresh_string {α : Type} (i : Nat) {n : Nat} : (Pat α n) -> (TupleN String n) × (Pat String n) × Nat :=
  Pat.fresh i (λ i => s!"x_{i}")

def Tm.num_vars {α : Type} (default : α) : Tm α -> Nat
  | Tm.hole => 0 
  | Tm.var _ => 1 
  | Tm.abs (Sigma.mk n (Case.mk p f)) =>
      let (vars, p', i) := Pat.fresh 0 (λ _ => default) p 
      have : sizeOf (f vars) < 1 + (1 + n + (1 + n + sizeOf p + sizeOf f)) := by 
        sorry
      let t' := f vars
      n + (Tm.num_vars default t')
  | Tm.app f a => (Tm.num_vars default f) + (Tm.num_vars default a)