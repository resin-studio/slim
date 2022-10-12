#eval Lean.versionString

@[reducible] def TupleN (α : Type) : Nat -> Type
  | 0 => Unit 
  | n + 1 => α × (TupleN α n)  

#check ((1, 2, ()) : TupleN Nat 2)
#check ((2, ()))


inductive Pat : (α : Type) -> Nat -> Type where
  | var : (x : α) -> Pat α 1
  | hole : Pat α 0 

inductive Tm (α : Type): Type
  | hole : Tm α 
  | var : α -> Tm α 
  | abs {n : Nat} : (Pat Unit n) -> (TupleN α n -> Tm α) -> Tm α
  | app : Tm α -> Tm α -> Tm α


def Pat.to_string {n : Nat} (t : Pat String n) := match t with
  | Pat.var x => s!"{x}" 
  | Pat.hole => s!"_" 

def Pat.fresh {α β : Type} (i : Nat) (f : Nat -> β) {n : Nat}  : (Pat α n) -> 
  (TupleN β n) × (Pat β n) × Nat 
  | Pat.var _ => ((f i, ()), (Pat.var (f i)), i + 1)
  | Pat.hole => ((), (Pat.hole), i)

def Pat.fresh_string {α : Type} (i : Nat) {n : Nat} : (Pat α n) -> (TupleN String n) × (Pat String n) × Nat :=
  Pat.fresh i (λ i => s!"x_{i}")


def Pat.vars {α : Type} {n : Nat} : (Pat α n) -> (TupleN α n) 
  | Pat.var x => (x, ()) 
  | Pat.hole => ()


def Tm.num_vars {α : Type} (default : α) : Tm α -> Nat
  | Tm.hole => 0 
  | Tm.var _ => 1 
  | @Tm.abs _ n p f =>
      let (vars, _, _) := Pat.fresh 0 (λ _ => default) p
      n + (Tm.num_vars default (f vars))
  | Tm.app f a => (Tm.num_vars default f) + (Tm.num_vars default a)


def Tm.to_string (i : Nat) : Tm String -> String
  | Tm.hole => "__"
  | Tm.var x => x 
  | Tm.abs p f => (
      let (vars, pat, i) := Pat.fresh_string i p 
      let param_str := Pat.to_string pat
      let body_str := Tm.to_string i (f vars)
      s!"(for {param_str}, {body_str})"
  )
  | Tm.app f a => s!"({Tm.to_string i f} {Tm.to_string i a})"


#check (Tm.abs (Pat.var ()) (fun (x, ()) => Tm.var x) : Tm String)

def dog : Tm String := Tm.abs (Pat.var ()) (fun (x, ()) => Tm.var x)
#eval Tm.to_string 0 dog


def holey : Tm String := Tm.abs (Pat.hole) (fun () => Tm.hole)

syntax "__" : term 
macro_rules
| `(__) => `(Tm.hole)

#check (__ : Tm String)

syntax "for " term " ::> " term : term 
macro_rules
| `(for $x ::> $y) => `(Tm.abs (Pat.var ()) (fun ($x, ()) => Tm.var $y))

#check ((for x ::> x): Tm String)

