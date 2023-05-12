import Std.Data.BinomialHeap
import Init.Data.Hashable
import Lean.Data.PersistentHashMap

open Lean PersistentHashMap
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

  def repr [Repr (α × β)] [BEq α] [Hashable α] 
  (m : PHashMap α β) (n : Nat) : Format :=
    Format.bracket "<" (List.repr (toList m) n) ">"

  instance [Repr (α × β)] [BEq α] [Hashable α] : Repr (PHashMap α β) where
    reprPrec := repr

  partial def intersect (m1 : PHashMap Nat Unit) (m2 : PHashMap Nat Unit) :=
    PHashMap.from_list (m1.toList.filter (fun (id, _) => m2.contains id))


end PHashMap


infixl:65   " ; " => PHashMap.insert_all

#check List.toArray

namespace List
  def index (f : α -> Bool) : (xs : List α) -> Option Nat 
  | [] => none 
  | x :: xs =>  
    if f x then
      some 0 
    else
      bind (index f xs) (fun n => some (1 + n))

end List