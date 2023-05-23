import Std.Data.BinomialHeap
import Init.Data.Hashable
import Lean.Data.PersistentHashMap
import Lean.Data.PersistentHashSet

open Lean PersistentHashMap PersistentHashSet
open Std

-- import Mathlib.Data.List.Sort

-- Sorting
-- copied from MathLib; import not working
section sorting
def split : List α → List α × List α
  | [] => ([], [])
  | a :: l =>
    let (l₁, l₂) := split l
    (a :: l₂, l₁)

partial def merge (r : α -> α -> Bool) : List α → List α → List α
  | [], l' => l'
  | l, [] => l
  | a :: l, b :: l' =>
    if r a b then a :: merge r l (b :: l') else b :: merge r (a :: l) l'

partial def mergeSort (r : α -> α -> Bool): List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: l => 
    let ls := (split (a :: b :: l))
    merge r (mergeSort r ls.1) (mergeSort r ls.2)

end sorting

namespace PHashMap

  def insert_all [BEq α] [Hashable α] 
  (base : PHashMap α β) (ext : PHashMap α β) : PHashMap α β :=
    ext.foldl (init := base) fun m k v => m.insert k v

  def from_list [BEq α] [Hashable α] 
  (source : List (α × β)) : PHashMap α β :=
    source.foldl (init := {}) fun m (k, v) => m.insert k v

  def as_set [BEq α] [Hashable α] 
  (source : List α) : PHashMap α Unit :=
    source.foldl (init := {}) fun m k => m.insert k Unit.unit

  def repr [Repr (α × β)] [BEq α] [Hashable α] 
  (m : PHashMap α β) (n : Nat) : Format :=
    Format.bracket "<" (List.repr (toList m) n) ">"

  instance [Repr (α × β)] [BEq α] [Hashable α] : Repr (PHashMap α β) where
    reprPrec := repr

  partial def intersect (m1 : PHashMap Nat Unit) (m2 : PHashMap Nat Unit) :=
    PHashMap.from_list (m1.toList.filter (fun (id, _) => m2.contains id))


end PHashMap


infixl:65   " ; " => PHashMap.insert_all

namespace PHashSet
  def toList  [BEq α] [Hashable α] (base : PHashSet α) : List α :=
    base.fold (fun acc k => k :: acc) []

  def insert_all [BEq α] [Hashable α] 
  (base : PHashSet α) (ext : PHashSet α) : PHashSet α :=
    ext.fold insert base

  def from_list [BEq α] [Hashable α] 
  (source : List α) : PHashSet α :=
    source.foldl (init := {}) fun m k => m.insert k

  def repr [Repr α] [BEq α] [Hashable α] 
  (m : PHashSet α) (n : Nat) : Format :=
    Format.bracket "{|" (List.repr (toList m) n) "|}"

  instance [Repr α] [BEq α] [Hashable α] : Repr (PHashSet α) where
    reprPrec := repr

  instance [BEq α] [Hashable α] : Add (PHashSet α) where
    add x y := x.fold insert y 

end PHashSet



namespace List
  def index (f : α -> Bool) : (xs : List α) -> Option Nat 
  | [] => none 
  | x :: xs =>  
    if f x then
      some 0 
    else
      bind (index f xs) (fun n => some (1 + n))

end List