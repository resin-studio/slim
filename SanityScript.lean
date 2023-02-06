import TestLib
import ProgramLib

open Lean PersistentHashMap




-- #eval [: β[0] :]
-- #eval [: β[0] :]

-- #check [: β[0] ∨ α[0] :]
-- #check [: β[0] ∧ α[0] :]
-- #check [: β[0] × α[0] :]
-- #check [: β[0] + α[0] :]
-- def x := 0
-- #check [: ∀ 1 :: β[0] ≤ α[0] => β[⟨x⟩] :]
-- #check [: ∀ 1 :: β[0] ≤ α[0] => β[0] :]
-- #check [: ∀ 2 :: α[0] ≤ α[0] => β[0] :]
-- #check [: ∀ 2 => β[0] :]
-- #check [: @ :]
-- #check [: α[24] :]
-- #check [: foo * @ :]
-- #check [: foo * @ ∨ (boo * @) :]
-- #check [: μ β[0] => foo * @ :]
-- #check [: foo * boo * @ :]
-- #check [: μ β[0] => foo * boo * @ :]
-- #check [: μ β[0] => foo * β[0] :]
-- #check [: μ β[0] => foo * β[0] ∧ α[0] ∨ α[2] ∧ α[0]:]
-- #check [: β[3] ∧ α[0] -> α[1] ∨ α[2] :]
-- #check [: μ β[0] => foo * β[0] ∧ α[0] ∨ α[2] ∧ α[0] -> α[1] ∨ α[2] :]
-- #check [: μ β[0] => foo * β[0] ∧ α[0] ∨ α[2] ∧ α[0] :]
-- #check [: α[0] :]

-- #eval [: ∀ 2 :: α[0] ≤ α[0] => β[0] :]
-- #eval [: μ β[0] => foo * β[0] ∧ α[0] ∨ α[2] ∧ α[0] :]



-- #eval ({} : PHashMap Nat Ty)

-- def zero_ := [: 
--     zero * @
-- :]


def main : IO Unit :=
  test [
    ("unfiy same tag ", unify_decide [: zero * @ :] [: zero * @ :] == true),
    ("unify diff tag", unify_decide [: zero * @ :] [: one * @ :] == false)
  ]


-- /-
--   μ nat .  zero*@ ∨ succ*nat 
-- -/
-- def nat_ := [: 
--   μ β[0] => zero*@ ∨ succ*β[0]
-- :]
-- #eval nat_

-- def even := [: 
--   μ β[0] => zero*@ ∨ succ*succ*β[0]
-- :]


-- def weven := [: 
--   μ β[0] => 
--     zero*@ ∨ 
--     succ*dumb*β[0]
-- :]

-- #eval unify_decide weven nat_ 
-- #eval unify_decide even nat_ 
-- #eval unify_decide nat_ even


-- #eval unify_decide
-- [: ∃ 2 :: β[0] ≤ ⟨even⟩ => β[0] × β[1]:] 
-- [: ∃ 2 :: β[0] ≤ ⟨nat_⟩ => β[0] × β[1]:] 

-- #eval unify_decide 
-- [: ∃ 2 :: ⟨even⟩ ≤ β[0] => β[0] × β[1]:] 
-- [: ∃ 2 :: ⟨nat_⟩ ≤ β[0] => β[0] × β[1]:] 

-- #eval unify_decide 
-- [: ∃ 2 :: β[0] ≤ ⟨nat_⟩ => β[0] × β[1]:] 
-- [: ∃ 2 :: β[0] ≤ ⟨even⟩ => β[0] × β[1]:] 

-- #eval unify_decide 
-- [: ∃ 2 :: ⟨nat_⟩ ≤ β[0] => β[0] × β[1]:] 
-- [: ∃ 2 :: ⟨even⟩ ≤ β[0] => β[0] × β[1]:] 

-- #eval unify_decide 
-- [: (zero*@) :] nat_ 

-- #eval unify_decide 
-- [: (succ*(zero*@)) :] nat_ 

-- #eval unify_decide 
-- [: (succ*(α[0])) :] 
-- nat_ 

-- #eval unify_reduce 
-- [: (succ*(α[0])) :] 
-- nat_ 
-- [: α[0] :]

-- def nat_list := [: 
--   μ β[0] => (
--     (l ~ zero*@ ∧ r ~ nil*@) ∨ 
--     (∃ 2 :: l ~ β[0] ∧ r ~ β[1] ≤ β[2] => 
--       (l ~ succ*β[0] ∧ r ~ cons*β[1]))
--   )
-- :]
-- --  ∧ / ∧  
-- def even_list := [: 
--   μ β[0] => (
--     (l ~ zero*@ ∧ r ~ nil*@) ∨ 
--     (∃ 2 :: l ~ β[0] ∧ r ~ β[1] ≤ β[2] => 
--       (l ~ succ*succ*β[0] ∧ r ~ cons*cons*β[1]))
--   )
-- :]

-- -- TODO
-- #eval unify_decide 
--   nat_list
--   even_list

-- #eval unify_decide 
--   even_list
--   nat_list

-- #eval unify_decide 
-- [: ∃ 1 :: β[0] ≤ ⟨even⟩ => hello * β[0] :]
-- [: ∃ 1 :: β[0] ≤ ⟨nat_⟩ => hello * β[0] :]

-- #eval unify_decide 
-- [: ∃ 1 :: β[0] ≤ ⟨nat_⟩ => hello * β[0] :]
-- [: ∃ 1 :: β[0] ≤ ⟨even⟩ => hello * β[0] :]

-- #eval unify_decide 
--   [: (l ~ zero*@ ∧ r ~ nil*@) :] 
--   nat_list

-- #eval unify_decide 
--   [: (l ~ zero*@ ∧ r ~ dumb*@) :] 
--   nat_list

-- -- this is record type is not wellformed 
-- #eval unify_decide 
--   [: (l ~ α[0] ∧ r ~ α[1]) :] 
--   nat_list

-- -- this is record type is not wellformed 
-- #eval unify_reduce
--   [: (l ~ α[0] ∧ r ~ α[1]) :] 
--   nat_list
--   [: ⊤ :]

-- #eval unify_decide 
--   [: (l ~ zero*@ ∧ r ~ α[0]) :] 
--   nat_list

-- -- expected α[0] → /nil
-- #eval unify_decide 
--   [: (l ~ succ*zero*@ ∧ r ~ cons*α[0]) :] 
--   nat_list

-- #eval unify_decide 
--   [: (l ~ succ*succ*zero*@ ∧ r ~ cons*α[0]) :] 
--   nat_list


-- #eval unify_reduce 
--   [: (l ~ succ*succ*zero*@ ∧ r ~ cons*α[0]) :] 
--   nat_list
--   [: α[0]:]


-- #eval unify_decide 
--   [: (l ~ succ*zero*@ ∧ r ~ cons*cons*α[0]) :] 
--   nat_list



-- def nat_to_list := [: 
--   ν β[0] => 
--     (zero*@ -> nil*@) ∧ 
--     (∀ 2 :: β[2] ≤ β[0] -> β[1] => 
--       succ*β[0] -> cons*β[1])
-- :]

-- #eval unify_decide 
--   nat_to_list
--   [: (succ*zero*@) -> (cons*nil*@) :] 

-- #eval unify_reduce 
--   nat_to_list
--   [: (succ*zero*@) -> (cons*nil*@) :] 
--   [: ⊤ :]

-- #eval unify_reduce
--   nat_to_list
--   [: (succ*zero*@ -> cons*α[0]) :] 
--   [: α[0] :]

-- #eval unify_reduce
--   nat_to_list
--   [: (succ*zero*@ -> cons*cons*α[0]) :] 
--   [: α[0] :]


-- /-
--   μ plus .
--     ∃ N .  
--       zero*@ × N × N | 

--     ∃ X Y Z :: X, Y, Z ≤ plus .  
--       succ*X × Y × succ*Z
-- -/
-- def plus := [: 
--   μ β[0] => 
--     (∃ 1 => 
--       (x ~ zero*@ ∧ y ~ β[0] ∧ z ~ β[0])) ∨ 

--     (∃ 3 :: (x ~ β[0] ∧ y ~ β[1] ∧ z ~ β[2]) ≤ β[3] => 
--       (x ~ succ*β[0] ∧ y ~ β[1] ∧ z ~ succ*β[2]))
-- :]

-- -- /print plus

-- -- #eval [: (x ~ zero*@ ∧ y ~ zero*@ ∧ z ~ zero*@) :]  
-- -- #eval [: succ*succ*zero*@ :]  


-- #eval unify_reduce [:
--     x ~ zero*@ ∧ 
--     y ~ α[0] ∧ 
--     z ~ zero*@
-- :] plus [: α[0] :]


-- #eval unify_reduce [:
--   (
--     x ~ (succ*zero*@) ∧ 
--     y ~ (succ*zero*@) ∧ 
--     z ~ (α[0])
--   )
-- :] plus [: α[0] :]


-- #eval unify_reduce [:
--   (
--     x ~ (succ*succ*zero*@) ∧ 
--     y ~ (succ*zero*@) ∧
--     z ~ (α[0])
--   )
-- :] plus
-- [: α[0] :]

-- #eval unify_reduce [:
--   (
--     x ~ (succ*zero*@) ∧ 
--     y ~ (α[0]) ∧
--     z ~ (succ*succ*zero*@)
--   )
-- :] plus
-- [: α[0] :]

-- #eval unify_reduce [:
--   (
--     x ~ (succ*zero*@) ∧
--     y ~ (succ*succ*zero*@) ∧
--     z ~ (α[0])
--   )
-- :] plus [: α[0] :]


-- -- expected: α[0] ↦ succ*zero*@
-- #eval unify_reduce [:
-- (
--   x ~ α[0] ∧
--   y ~ succ*zero*@ ∧
--   z ~ succ*succ*zero*@
-- )
-- :] plus
-- [: α[0] :]


-- #eval unify_reduce [:
-- (
--   x ~ succ*zero*@ ∧
--   y ~ α[0] ∧
--   z ~ succ*succ*zero*@
-- )
-- :] plus
-- [: α[0] :]


-- #eval unify_reduce [:
-- (
--   x ~ (α[0]) ∧
--   y ~ (α[1]) ∧
--   z ~ (succ*succ*zero*@)
-- )
-- :] plus
-- [: x ~ α[0] ∧ y ~ α[1] :]

-- #eval unify_reduce [:
-- (
--   x ~ (succ*succ*zero*@) ∧
--   y ~ (α[1]) ∧
--   z ~ (α[0])
-- )
-- :] plus
-- [: y ~ α[1] ∧ z ~ α[0] :]


-- -- term testing
-- #eval [:
--   λ[ 
--     for y[0] : α[0] => y[0],
--     for y[0] : α[0] => y[0] 
--   ]
-- :]

-- #eval [:
--   ω[ 
--     left := x[0],
--     right := x[0]
--   ]
-- :]


-- #eval [:
--   succ;zero;()
-- :]



-- #eval infer_reduce [:
--   succ;zero;()
-- :]

-- #eval [:
--   succ;zero;()
-- :]

-- #eval [:
--   x[0]/hello
-- :]

-- #eval infer_reduce [:
--   _ 
-- :]


-- #eval [:
--   α[0] + α[1]
-- :]

-- #eval [:
--   α[0] × α[1]
-- :]

-- #eval [:
--   (x[0], x[1])
-- :]


-- #eval infer_reduce [:
--   λ [for y[0] => y[0]]
-- :]

-- #eval infer_reduce [:
--   λ [for y[0] : abc*@ => y[0]]
-- :]

-- #eval infer_reduce [:
--   λ [for y[0] : inp*@ -> out*@ =>
--   Out ; λ [for y[0] => 
--       cons ; ((y[1] y[0]), nil ; ())
--   ]
--   ]
-- :]

-- #eval infer_reduce [:
--   ((), nil ; ())
-- :]

  
-- #eval [:
--   hello*thing~@
  
-- :]

-- #eval infer_reduce [:
--   λ y[0] : nat*@ =>
--     let y[0] = (λ (y[0], y[1]) : (str*@ × str*@) => y[0]) =>
--     (y[0] (str;(), str;()))
-- :]

-- #eval infer_reduce [:
--   λ y[0] : nat*@ =>
--     let y[0] = (λ (y[0], y[1]) : (str*@ × str*@) => y[0]) =>
--     (y[0] (_, str;()))
-- :]

-- #eval infer_reduce [:
--   λ y[0] : nat*@ =>
--     let y[0] = λ[for (y[0], y[1]) : (str*@ × str*@) => y[0]] =>
--     (y[0] (y[1], _))
-- :]

-- -- Propagation: Down 
-- -- even though, there is a hole in the program,
-- -- the type of α[0] can be inferred to be uno*@  
-- -- due to the application and downward propagation
-- #eval infer_reduce [:
--   λ y[0] : α[0] =>
--     let y[0] = (λ (y[0], y[1]) : (uno*@ × dos*@) => y[1]) =>
--     (y[0] (y[1], _))
-- :]

-- -- Propagation: Up
-- #eval infer_reduce [:
--   λ y[0] : hello*@ -> world*@ =>
--   λ y[0] => 
--     (cons ; ((y[1] y[0]), nil ; ()))
-- :]

-- #eval infer_reduce [:
--   λ y[0] : int*@ -> str*@ => 
--   λ y[0] : int*@  =>
--     (y[1] y[0])
-- :]


-- #eval infer_reduce [:
--   λ y[0] : str*@ -> @ => 
--   λ y[0] : str*@ => 
--      (OUTPUT ; (y[1] y[0]))
-- :]

-- #eval infer_reduce [:
--   λ y[0] : int*@ -> @ => 
--   λ y[0] : str*@ => 
--      (y[1] y[0]) 
-- :]

-- #eval infer_reduce [:
--   λ y[0] : (int*@ ∨ str*@) -> @ => 
--   λ y[0] : str*@ => 
--      (y[1] y[0]) 
-- :]

-- #eval infer_reduce [:
--   λ y[0] : (int*@ ∨ α[1]) -> α[1] => 
--   λ y[0] : str*@ => 
--      (y[1] y[0]) 
-- :]

-- #eval infer_reduce [:
--   λ y[0] : ∀ 1 => (β[0] -> β[0]) => 
--   λ y[0] : int*@  =>
--     (y[1] y[0])
-- :]



-- -----

-- -- Widening
-- #eval infer_reduce [:
--   λ y[0] : α[1] -> (α[1] -> (α[1] × α[1])) => 
--     (OUTPUT ; (y[0] hello;()))
-- :]

-- -- Widening
-- #eval infer_reduce [:
--   λ y[0] : α[1] -> (α[1] -> (α[1] × α[1])) => 
--     (OUTPUT ; ((y[0] hello;()) world;()))
-- :]


-- -- Widening
-- #eval infer_reduce [:
--   λ y[0] : α[1] -> (α[1] -> (α[1] × α[1])) => 
--   λ y[0] : hello*@ =>
--   λ y[0] : world*@ =>
--     OUTPUT ; ((y[2] y[1]) y[0])
-- :]

-- -- Widening
-- #eval infer_reduce [:
--   λ y[0] : ∀ 1 => β[0] -> β[0] -> (β[0] × β[0]) => 
--   λ y[0] : hello*@ =>
--   λ y[0] : world*@ =>
--     OUTPUT ; ((y[2] y[1]) y[0])
-- :]

-- #eval infer_reduce [:
--   λ y[0] : α[1] -> (α[1] -> (α[1] × α[1])) => 
--   let y[0] = ((y[0] hello;()) world;()) =>
--     OUTPUT ; y[0]
-- :]


-- #eval infer_reduce [:
--   λ y[0] : ∀ 1 => β[0] -> β[0] -> (β[0] × β[0]) => 
--   λ y[0] : int*@  =>
--   λ y[0] : str*@  =>
--   let y[0] = ((y[2] y[1]) y[0]) =>
--   OUTPUT ; y[0]
-- :]

-- #eval infer_reduce [:
--   let y[0] = (hello ; ()) =>
--   y[0]
-- :]

-- -- Narrowing

-- #eval [:
--   λ y[0] : uno*@ -> @ => y[0]
-- :]
-- #eval [:
--   λ y[0] : uno*@ -> @ => 
--   λ y[0] : dos*@ -> @ =>
--   λ y[0] =>
--     ((y[2] y[0]), (y[1] y[0]))
-- :]
-- #eval infer_reduce [:
--   λ y[0] : uno*@ -> @ => 
--   λ y[0] : dos*@ -> @ =>
--   OUTPUT ; (
--     λ y[0] => ((y[2] y[0]), (y[1] y[0]))
--   )
-- :]
-- #eval infer_reduce [:
--   λ y[0] : uno*@ -> @ => 
--   λ y[0] : dos*@ -> @ =>
--   OUTPUT ; (λ y[0] =>
--     ((y[2] y[0]), (y[1] y[0]))
--   )
-- :]

-- -- let-polymorphism: how generic?

-- -- not generic
-- #eval infer_reduce [:
--   ((λ y[0] : ⟨nat_⟩ => y[0]) zero;())
-- :]

-- -- not generic
-- #eval infer_reduce [:
--   let y[0] = (λ y[0] : ⟨nat_⟩ => y[0]) =>
--   (y[0] zero;())
-- :]

-- -- not generic
-- #eval infer_reduce [:
--   let y[0] = (λ y[0] : ⟨nat_⟩ => y[0]) =>
--   y[0]
-- :]

-- -- expected: ⊥ 
-- #eval infer_reduce [:
--   let y[0] : (∀ 1 :: β[0] ≤ ⟨nat_⟩ => β[0] -> β[0]) = (λ y[0] : ⟨nat_⟩ => y[0]) =>
--   y[0]
-- :]

-- -- expected: true 
-- #eval unify_decide 
-- [: (∀ 1 :: β[0] ≤ ⟨nat_⟩ => β[0] -> β[0]) :]
-- [: ⟨nat_⟩ -> ⟨nat_⟩ :]

-- -- expected: false 
-- #eval unify_decide 
-- [: ⟨nat_⟩ -> ⟨nat_⟩ :]
-- [: (∀ 1 :: β[0] ≤ ⟨nat_⟩ => β[0] -> β[0]) :]


-- #eval infer_reduce [:
--   let y[0] : (∀ 1 :: ⟨nat_⟩ ≤ β[0] => β[0] -> β[0]) = (λ y[0] : ⟨nat_⟩ => y[0]) =>
--   y[0]
-- :]

-- -- generic enough
-- -- but too redundant
-- #eval infer_reduce [:
--   let y[0] : (∀ 1 :: β[0] ≤ ⟨nat_⟩ => β[0] -> β[0]) = (λ y[0] => y[0]) =>
--   (y[0] zero;())
-- :]



-- #eval infer_reduce [:
--   let y[0] = (λ y[0] => y[0]) =>
--   (y[0] zero;())
-- :]

-- #eval infer_reduce [:
--   let y[0] = (λ y[0] => y[0]) =>
--   y[0]
-- :]

-- #eval infer_reduce [:
--   let y[0] = (λ y[0] : ⟨nat_⟩ => ()) =>
--   let y[0] = (λ y[0] => ((y[1] y[0]), y[0])) =>
--   (y[0] zero;())
-- :]

-- -- let-polymorphism

-- #eval infer_reduce [:
--   let y[0] = (λ y[0] : str*@ => hello ; y[0]) =>
--   (y[0] str;())
-- :]

-- #eval infer_reduce [:
--   let y[0] = (λ y[0] => hello ; y[0]) =>
--   (
--     y[0]
--   )
-- :]

-- #eval infer_reduce [:
--   let y[0] = (λ y[0] => hello ; y[0]) =>
--   (y[0] uno;())
-- :]


-- #eval infer_reduce [:
--   let y[0] = (λ y[0] => hello ; y[0]) =>
--   (
--     (y[0] uno;()),
--     (y[0] dos;())
--   )
-- :]




-- def repli := [:
--   ∀ 1 => β[0] -> (ν β[0] =>
--     (zero*@ -> nil*@) ∧
--     (∀ 2 :: β[2] ≤ (β[0] -> β[1]) =>
--       succ*β[0] -> cons*(β[3] × β[1])
--     )
--   )
-- :]


-- -----

-- #eval unify_decide 
-- [: uno ~ @ ∧ dos ~ @ ∧ tres ~ @:]
-- [: uno ~ @ ∧ tres ~ @:]

-- #eval unify_decide 
-- [: uno ~ @ ∧ dos ~ @ ∧ tres ~ @:]
-- [: ∀ 1 :: β[0] ≤ uno ~ @ ∨ dos ~ @ ∨ tres ~ @ => β[0]:]

-- #eval unify_decide 
-- [: ∀ 1 :: β[0] ≤ uno ~ @ ∨ dos ~ @ ∨ tres ~ @ => β[0]:]
-- [: uno ~ @ ∧ dos ~ @ ∧ tres ~ @:]


-- #eval unify_decide 
-- [: uno ~ @ ∨ dos ~ @ ∨ tres ~ @ :]
-- [:dos ~ @ ∧ tres ~ @ :]

-- #eval unify_decide 
-- [:dos ~ @ ∧ tres ~ @ ∧ four ~ @:]
-- [: uno ~ @ ∨ dos ~ @ ∨ tres ~ @ :]

-- #eval unify_decide 
-- [: ∀ 1 :: β[0] ≤ uno ~ @ ∨ dos ~ @ ∨ tres ~ @ => β[0]:]
-- [:dos ~ @ ∧ tres ~ @ ∧ four ~ @:]

-- #eval unify_decide 
-- [: ∀ 1 :: uno ~ @ ∧ dos ~ @ ∧ tres ~ @ ≤ β[0] => β[0]:]
-- [:dos ~ @ ∧ tres ~ @ :]

-- #eval unify_decide 
-- [: ∀ 1 :: uno ~ @ ∧ dos ~ @ ∧ tres ~ @ ≤ β[0] => β[0]:]
-- [: ∀ 1 :: uno ~ @ ∧ dos ~ @ ≤ β[0] => β[0]:]

-- #eval unify_decide 
-- [: ∀ 1 :: uno ~ @ ∧ dos ~ @ ≤ β[0] => β[0]:]
-- [: ∀ 1 :: uno ~ @ ∧ dos ~ @ ∧ tres ~ @ ≤ β[0] => β[0]:]

-- #eval unify_decide 
-- [: ∀ 1 :: β[0] ≤ ⟨even⟩ => hello * β[0] :]
-- [: ∀ 1 :: β[0] ≤ ⟨nat_⟩ => hello * β[0] :]

-- #eval unify_decide 
-- [: ∀ 1 :: β[0] ≤ ⟨nat_⟩ => hello * β[0] :]
-- [: ∀ 1 :: β[0] ≤ ⟨even⟩ => hello * β[0] :]

-- #eval unify_decide 
-- [: ∀ 1 :: uno ~ @ ∧ dos ~ @ ∧ tres ~ @ ≤ β[0] => β[0]:]
-- [: ∀ 1 :: uno ~ @ ∧ dos ~ @ ∧ four ~ @ ≤ β[0] => β[0]:]

-- #eval unify_decide 
-- [: ∀ 1 :: β[0] ≤ uno ~ @ => β[0]:]
-- [:uno ~ @ ∧ four ~ @:]

-- #eval unify_decide 
-- [: ∀ 1 :: uno ~ @ ≤ β[0] => β[0]:]
-- [:uno ~ @ ∧ four ~ @:]


-- ----- 

-- def nat_to_unit := [: 
--   ν β[0] => 
--     (zero*@ -> @) ∧ 
--     (∀ 1 :: β[1] ≤ β[0] -> @ => 
--       (succ*β[0]) -> @) 
-- :]

-- def even_to_unit := [: 
--   ν β[0] => 
--     (zero*@ -> @) ∧ 
--     (∀ 1 :: β[1] ≤ β[0] -> @ => 
--       (succ*succ*β[0]) -> @)
-- :]

-- #eval unify_decide 
-- nat_to_unit
-- [: (zero*@ -> @) :]

-- #eval unify_decide 
-- nat_to_unit
-- nat_to_unit

-- #eval unify_decide 
-- nat_to_unit
-- [: (succ*zero*@ -> @) :]

-- #eval unify_decide 
-- even_to_unit
-- [: (succ*succ*zero*@ -> @) :]

-- #eval unify_decide 
-- even_to_unit
-- [: (succ*zero*@ -> @) :]

-- -- -- TODO: why does this diverge?
-- -- #eval unify 3 {} Ty.top 
-- -- [: 
-- --     (zero*@ -> @) ∧ 
-- --     (∀ 1 :: ⟨nat_to_unit⟩ ≤ β[0] -> @ => 
-- --       (succ*β[0]) -> @) 
-- -- :]
-- -- [: 
-- --     (zero*@ -> @) ∧ 
-- --     (∀ 1 :: ⟨nat_to_unit⟩ ≤ β[0] -> @ => 
-- --       (succ*succ*β[0]) -> @)
-- -- :]

-- -- #eval unify 3 {} Ty.top 
-- -- nat_to_unit
-- -- even_to_unit

-- -- #eval unify 3 {} Ty.top 
-- -- even_to_unit
-- -- nat_to_unit

-- -- #eval unify 3 {} Ty.top 
-- -- nat_
-- -- even

-- #eval repli

-- #eval [:
--   λ y[0] => fix (λ y[0] => λ[
--   for zero;() => nil;(),
--   for succ;y[0] => cons;(y[2], (y[1] y[0])) 
--   ]) 
-- :]


-- #eval infer_reduce [:
--   λ[
--   for zero;() => nil;(),
--   for succ;y[0] => cons;((), ()) 
--   ] 
-- :]


-- #eval [: (zero*@ -> nil*@) ∧ (succ*⊤ -> cons*(@ × ⊥)) :]

-- #eval unify_reduce
-- [: α[2] -> ((zero*@ -> nil*@) ∧ (succ*⊤ -> cons*(@ × @))) :]
-- [: α[0] -> α[0] :]
-- [: α[0] :]

-- #eval infer_reduce_wt 
-- [:
--   (λ y[0] => λ[
--   for zero;() => nil;(),
--   for succ;y[0] => cons;((), (y[1] y[0])) 
--   ]) 
-- :]
-- [: α[20] -> α[20] :]


-- #eval [:
--   ∀ 1 => β[0] -> (ν β[0] =>
--     (zero*@ -> nil*@) ∧
--     (∀ 2 :: β[2] ≤ (β[0] -> β[1]) =>
--       succ*β[0] -> cons*(β[3] × β[1])
--     )
--   )
-- :]

-- #eval unify_reduce
-- [: (α[0] -> α[1]) -> ((zero*@ -> nil*@) ∧ (succ*α[0] -> cons*(@ × α[1]))) :]
-- [: α[20] -> α[20] :]
-- [: α[20] :]


-- #eval infer_reduce [:
--   fix (λ y[0] => λ[
--   for zero;() => nil;(),
--   for succ;y[0] => cons;((), (y[1] y[0])) 
--   ]) 
-- :]

-- #eval infer_reduce_wt [:
--   fix (λ y[0] => λ[
--   for zero;() => nil;(),
--   for succ;y[0] => cons;((), (y[1] y[0])) 
--   ]) 
-- :]
-- [:
--   (zero*@ -> nil*@)
-- :]


-- #eval infer_reduce_wt [:
--   (λ y[0] => λ[
--   for zero;() => nil;(),
--   for succ;y[0] => cons;((), (y[1] y[0])) 
--   ]) 
-- :]
-- [:
--   (zero*@ -> nil*@)
--   ->
--   (zero*@ -> nil*@)
-- :]

-- #eval infer_reduce_wt [:
--   fix (λ y[0] => λ[
--   for zero;() => nil;(),
--   for succ;y[0] => cons;((), (y[1] y[0])) 
--   ]) 
-- :]
-- [:
--   ν β[0] => 
--   (∀ 2 :: β[2] ≤ (β[0] -> β[1]) => 
--     (zero*@ -> nil*@) ∧ 
--     (succ*β[0] -> cons*(@ × β[1]))
--   )
-- :]


-- #eval infer_reduce_wt [:
--   fix (λ y[0] => λ[
--   for zero;() => nil;(),
--   for succ;y[0] => cons;((), (y[1] y[0])) 
--   ]) 
-- :]
-- [:
--   ν β[0] => 
--   (
--     (zero*@ -> nil*@) ∧ 
--     (∀ 2 :: β[2] ≤ (β[0] -> β[1]) => 
--       (succ*β[0] -> cons*(@ × β[1]))
--     )
--   )
-- :]


-- #eval infer_reduce
-- [:
--   λ y[0] : (ν β[0] => 
--     (
--       (zero*@ -> nil*@)
--     )
--   ) => (y[0] (zero;()))
-- :]


-- #eval infer_reduce
-- [:
--   λ y[0] : (ν β[0] => 
--     (
--       (zero*@ -> nil*@) ∧ 
--       (∀ 2 :: β[2] ≤ (β[0] -> β[1]) => 
--         (succ*β[0] -> cons*(@ × β[1]))
--       )
--     )
--   ) => (y[0] (succ;zero;()))
-- :]

-- #eval infer_reduce
-- [:
--   λ y[0] : (ν β[0] => 
--     (
--       (zero*@ -> nil*@) ∧ 
--       (∀ 2 :: β[2] ≤ (β[0] -> β[1]) => 
--         (succ*β[0] -> cons*(@ × β[1]))
--       )
--     )
--   ) => (y[0] (succ;_))
-- :]

-- #eval infer_reduce
-- [:
--   λ y[0] : (ν β[0] => 
--     (
--       (zero*@ -> nil*@) ∧ 
--       (∀ 2 :: β[2] ≤ (β[0] -> β[1]) => 
--         (succ*β[0] -> cons*(@ × β[1]))
--       )
--     )
--   ) => (y[0] (succ;succ;_))
-- :]

-- #eval infer_reduce [:
--   λ y[0] : (
--     ν β[0] => ∀ 2 :: β[2] ≤ (β[1] -> β[0]) =>
--     ((zero*@ -> nil*@) ∧ (succ*β[1] -> cons*(@ × β[0])))
--   ) => (y[0] (succ;_))
-- :]

-- #eval infer_reduce [:
--   λ y[0] : (
--     ν β[0] => ∀ 2 :: β[2] ≤ (β[1] -> β[0]) =>
--     ((zero*@ -> nil*@) ∧ (succ*β[1] -> cons*(@ × β[0])))
--   ) => (y[0] (succ;succ;_))
-- :]

-- #eval infer_reduce [:
--   λ y[0] : (
--     ∀ 0 :: ⊥ ≤ ⊤ => (
--       ν β[0] => ∀ 2 :: β[2] ≤ (β[1] -> β[0]) =>
--       ((zero*@ -> nil*@) ∧ (succ*β[1] -> cons*(@ × β[0])))
--     )
--   ) => (y[0] (zero;()))
-- :]

-- ---------

-- #eval infer_reduce [:
--   let y[0] : (
--     ν β[0] => ∀ 2 :: β[2] ≤ (β[1] -> β[0]) =>
--     ((zero*@ -> nil*@) ∧ (succ*β[1] -> cons*(@ × β[0])))
--   ) = _ => (y[0] (zero;()))
-- :]

-- #eval infer_reduce [:
--   let y[0] : (
--     ν β[0] => ∀ 2 :: β[2] ≤ (β[1] -> β[0]) =>
--     ((zero*@ -> nil*@) ∧ (succ*β[1] -> cons*(@ × β[0])))
--   ) = _ => (y[0] (succ;succ;zero;()))
-- :]

-- #eval infer_reduce [:
--   let y[0] : (
--     ν β[0] => ∀ 2 :: β[2] ≤ (β[1] -> β[0]) =>
--     ((zero*@ -> nil*@) ∧ (succ*β[1] -> cons*(@ × β[0])))
--   ) = _ => (y[0] (succ;succ;_))
-- :]

-- #eval infer_reduce [:
--   let y[0] : (
--     ν β[0] => ∀ 2 :: β[2] ≤ (β[1] -> β[0]) =>
--     ((zero*@ -> nil*@) ∧ (succ*β[1] -> cons*(@ × β[0])))
--   ) = _ => y[0]
-- :]


-- #eval infer_reduce [:
--   let y[0] : (
--     ν β[0] => ∀ 2 :: β[2] ≤ (β[1] -> β[0]) =>
--       ((zero*@ -> nil*@) ∧ ((succ*β[1] -> cons*(l ~ @ ∧ (r ~ β[0] ∧ ⊤))) ∧ ⊤))
--   ) = _ => (y[0] (succ;succ;zero;()))
-- :]


-- #eval unify_decide 
-- [:
--   ν β[0] => ∀ 2 :: β[2] ≤ (β[1] -> β[0]) =>
--     ((zero*@ -> nil*@) ∧ ((succ*β[1] -> cons*(l ~ @ ∧ (r ~ β[0] ∧ ⊤))) ∧ ⊤))
-- :]
-- [:
--   α[0] -> α[1]
-- :]

-- #eval unify_decide 
-- [:
--   ν β[0] => ∀ 2 :: β[2] ≤ (β[1] -> β[0]) =>
--     (zero*@ -> nil*@) ∧ ((succ*β[1] -> cons*(l ~ @ ∧ r ~ β[0])))
-- :]
-- [:
--   α[0] -> α[1]
-- :]

-- #eval infer_reduce [:
--   let y[0] = fix(λ y[0] => λ[
--   for zero;() => nil;(),
--   for succ;y[0] => cons;((), (y[1] y[0])) 
--   ]) => 
--   (y[0] succ;zero;())
-- :]


-- #eval infer_reduce [:
--   let y[0] = fix(λ y[0] => λ[
--   for zero;() => nil;(),
--   for succ;y[0] => cons;((), (y[1] y[0])) 
--   ]) => 
--   y[0]
-- :]

-- #eval infer_test [:
--   let y[0] = fix(λ y[0] => λ[
--   for zero;() => nil;(),
--   for succ;y[0] => cons;((), (y[1] y[0])) 
--   ]) => 
--   y[0]
-- :]
-- [: α[30] :]

-- #eval infer_test [:
--   let y[0] : (
--     ν β[0] => ∀ 2 :: β[2] ≤ (β[1] -> β[0]) =>
--     ((zero*@ -> nil*@) ∧ (succ*β[1] -> cons*(@ × β[0])))
--   ) = _ => y[0]
-- :]
-- [: α[30] :]

-- #eval infer_reduce [:
--   let y[0] = fix(λ y[0] => λ[
--   for zero;() => nil;(),
--   for succ;y[0] => cons;((), (y[1] y[0])) 
--   ]) => 
--   (y[0] (zero;()))
-- :]


-- -- TODO: why does this fail?
-- #eval infer_reduce [:
--   let y[0] : ⟨nat_⟩ = _ =>
--   let y[0] = fix(λ y[0] => λ[
--   for zero;() => nil;(),
--   for succ;y[0] => cons;((), (y[1] y[0])) 
--   ]) => 
--   (y[0] y[1])
-- :]

-- #eval infer_reduce [:
--   let y[0] : ⟨nat_⟩ = _ =>
--   let y[0] = fix(λ y[0] => λ[
--   for zero;() => nil;(),
--   for succ;y[0] => cons;((), (y[1] y[0])) 
--   ]) => 
--   y[1]
-- :]

-- #eval (extract_premise 0 [: 
--     ∀ 2 :: β[2] ≤ (β[1] -> β[0]) =>
--     ((zero*@ -> nil*@) ∧ (succ*β[1] -> cons*(@ × β[0])))
-- :])

-- #eval unify_decide
-- nat_
-- [:
-- μ β[0] => ∃ 2 :: β[1] ≤ β[2] =>
-- zero*@ ∨ 
-- succ*β[1]
-- :]


-- -- TODO: figure out why this fails
-- #eval infer_test [:
--   fix(λ y[0] => λ[
--   for zero;() => nil;(),
--   for succ;y[0] => cons;((), (y[1] y[0])) 
--   ]) 
-- :] [:
--   ν β[0] => ∀ 2 :: β[2] ≤ (β[1] -> β[0]) =>
--   ((zero*@ -> nil*@) ∧ (succ*β[1] -> cons*(@ × β[0])))
-- :]

-- #eval unify_decide [:
--   ν β[0] => ∀ 2 :: β[2] ≤ (β[1] -> β[0]) =>
--   ((zero*@ -> nil*@) ∧ (succ*β[1] -> cons*(@ × β[0])))
-- :] [:
--   ν β[0] => ∀ 2 :: β[2] ≤ (β[1] -> β[0]) =>
--   ((zero*@ -> nil*@) ∧ (succ*β[1] -> cons*(@ × β[0])))
-- :]

-- -- TODO: why does this fail?
-- #eval unify_decide [:
--   ν β[0] => ∀ 2 :: β[2] ≤ (β[1] -> β[0]) =>
--   ((zero*@ -> nil*@) ∧ (succ*β[1] -> cons*(@ × β[0])))
-- :] [:
--   ∀ 1 :: β[0] ≤ (⟨nat_⟩) =>
--     (β[0] -> (∃ 1 :: (β[1] × β[0]) ≤ ⟨nat_list⟩ => β[0]))
-- :]

-- #eval unify_decide [:
--   ∀ 1 :: β[0] ≤ (⟨nat_⟩) =>
--     (β[0] -> (∃ 1 :: (β[1] × β[0]) ≤ ⟨nat_list⟩ => β[0]))
-- :] [:
--   ν β[0] => ∀ 2 :: β[2] ≤ (β[1] -> β[0]) =>
--   ((zero*@ -> nil*@) ∧ (succ*β[1] -> cons*(@ × β[0])))
-- :]


-- -- TODO: figure out why this fails
-- #eval infer_reduce_wt [:
--   (λ y[0] => λ[
--   for zero;() => nil;(),
--   for succ;y[0] => cons;((), (y[1] y[0])) 
--   ]) 
-- :]
-- [:
--   (ν β[0] => ∀ 2 :: β[2] ≤ (β[0] -> β[1]) =>
--     ((zero*@ -> nil*@) ∧ (succ*β[0] -> cons*(@ × β[1])))
--   )
--   ->
--   (ν β[0] => ∀ 2 :: β[2] ≤ (β[0] -> β[1]) =>
--     ((zero*@ -> nil*@) ∧ (succ*β[0] -> cons*(@ × β[1])))
--   )
-- :]


-- #eval infer_reduce [:
--   fix(λ y[0] => λ[
--   for zero;() => nil;(),
--   for succ;y[0] => cons;((), (y[1] y[0])) 
--   ]) 
-- :]

-- #eval infer_reduce [:
--   let y[0] = fix(λ y[0] => λ[
--   for zero;() => nil;(),
--   for succ;y[0] => cons;((), (y[1] y[0])) 
--   ]) => 
--   y[0]
-- :]

-- #eval unify_reduce 
-- [:
--   (ν β[0] => 
--     (
--       (zero*@ -> nil*@) ∧ 
--       (∀ 2 :: β[2] ≤ (β[0] -> β[1]) => 
--         (succ*β[0] -> cons*(@ × β[1]))
--       )
--     )
--   )
-- :]
-- [:
--   α[0] -> α[1]
-- :]
-- [: α[0] :]



-- #eval extract_premise 0 [:
--     (
--       (zero*@ -> nil*@) ∧ 
--       (∀ 2 :: β[2] ≤ (β[0] -> β[1]) => 
--         (succ*β[0] -> cons*(@ × β[1]))
--       )
--     )
-- :]

-- #eval rewrite_function_type [:
--   ν β[0] =>
--     (
--       (zero*@ -> nil*@) ∧ 
--       (∀ 2 :: β[2] ≤ (β[0] -> β[1]) => 
--         (succ*β[0] -> cons*(@ × β[1]))
--       )
--     )
-- :]


-- #eval unify_reduce
-- [:
--   (∀ 1 :: β[0] ≤ (μ β[0] => zero*@ ∨ (∃ 2 :: β[0] ≤ β[2] => succ*β[0])) =>
--     (β[0] ->
--       (∃ 1 :: 
--         (β[1] × β[0]) ≤ (μ β[0] => 
--           (zero*@ × nil*@) ∨
--           (∃ 2 :: (β[0] × β[1]) ≤ β[2] => (succ*β[0] × cons*(@ × β[1])))
--         ) =>
--         β[0]
--       )
--     )
--   )
-- :]
-- [: α[0] -> α[1] :]
-- [: α[1] :]

-- -- false: why does this fail?
-- -- ∀ can't be instantiated 
-- -- safe to fail, but not lenient
-- #eval unify_decide [:
--   ν β[0] => ∀ 2 :: β[2] ≤ (β[1] -> β[0]) =>
--   ((zero*@ -> nil*@) ∧ (succ*β[1] -> cons*(@ × β[0])))
-- :] [:
--   ∀ 1 :: β[0] ≤ (⟨nat_⟩) =>
--     (β[0] -> (∃ 1 :: (β[1] × β[0]) ≤ ⟨nat_list⟩ => β[0]))
-- :]

-- -- false: why does this fail?
-- -- ν can't be unrolled
-- -- safe to fail, but not lenient
-- #eval unify_decide 
-- [:
--   ∀ 1 :: β[0] ≤ (⟨nat_⟩) =>
--     (β[0] -> (∃ 1 :: (β[1] × β[0]) ≤ ⟨nat_list⟩ => β[0]))
-- :]
-- [:
--   ν β[0] => ∀ 2 :: β[2] ≤ (β[1] -> β[0]) =>
--   ((zero*@ -> nil*@) ∧ (succ*β[1] -> cons*(@ × β[0])))
-- :] 

-- #eval unify_decide [:
--   (∀ 1 :: β[0] ≤ (μ β[0] => zero*@ ∨ (∃ 2 :: β[0] ≤ β[2] => succ*β[0])) =>
--     (β[0] ->
--       (∃ 1 :: 
--         (β[1] × β[0]) ≤ (μ β[0] => 
--           (zero*@ × nil*@) ∨
--           (∃ 2 :: (β[0] × β[1]) ≤ β[2] => (succ*β[0] × cons*(@ × β[1])))
--         ) =>
--         β[0]
--       )
--     )
--   )
-- :] [:
--   (∀ 1 :: β[0] ≤ (μ β[0] => zero*@ ∨ (∃ 2 :: β[0] ≤ β[2] => succ*β[0])) =>
--     (β[0] ->
--       (∃ 1 :: 
--         (β[1] × β[0]) ≤ (μ β[0] => 
--           (zero*@ × nil*@) ∨
--           (∃ 2 :: (β[0] × β[1]) ≤ β[2] => (succ*β[0] × cons*(@ × β[1])))
--         ) =>
--         β[0]
--       )
--     )
--   )
-- :]

-- -- TODO: why does this fail?
-- #eval unify_decide [:
--   (∀ 1 :: β[0] ≤ ⟨nat_⟩ =>
--     (β[0] ->
--       (∃ 1 :: 
--         (β[1] × β[0]) ≤ ⟨nat_list⟩ =>
--         β[0]
--       )
--     )
--   )
-- :] [:
--   (∀ 1 :: β[0] ≤ ⟨nat_⟩ =>
--     (β[0] ->
--       (∃ 1 :: 
--         (β[1] × β[0]) ≤ ⟨nat_list⟩ =>
--         β[0]
--       )
--     )
--   )
-- :]

-- #eval unify_decide even nat_

-- #eval unify_decide [:
--   ⟨nat_⟩ -> @
-- :] [:
--   ⟨even⟩ -> @ 
-- :]

-- -- expected: true
-- #eval unify_decide [:
--   (∀ 1 :: β[0] ≤ ⟨nat_⟩ =>
--     (β[0] -> @)
--   )
-- :] [:
--   (∀ 1 :: β[0] ≤ ⟨even⟩ =>
--     (β[0] -> @)
--   )
-- :]

-- -- expected: false 
-- #eval unify_decide [:
--   (∀ 1 :: β[0] ≤ ⟨even⟩ =>
--     (β[0] -> @)
--   )
-- :] [:
--   (∀ 1 :: β[0] ≤ ⟨nat_⟩ =>
--     (β[0] -> @)
--   )
-- :]

-- -- expected: true
-- #eval unify_decide [:
--   (∀ 1 :: β[0] ≤ ⟨nat_⟩ =>
--     (β[0])
--   )
-- :] [:
--   (∀ 1 :: β[0] ≤ ⟨even⟩ =>
--     (β[0])
--   )
-- :]

-- -- expected: false 
-- -- this is overly strict, but safe 
-- -- there is no way for the LHS to know to instantiate with ⊥ vs nat_
-- #eval unify_decide [:
--   (∀ 1 :: β[0] ≤ ⟨even⟩ =>
--     (β[0])
--   )
-- :] [:
--   (∀ 1 :: β[0] ≤ ⟨nat_⟩ =>
--     (β[0])
--   )
-- :]

-- -- expected: true 
-- #eval unify_decide [:
--   (∀ 1 :: ⟨even⟩ ≤ β[0] =>
--     (β[0])
--   )
-- :] [:
--   (∀ 1 :: ⟨nat_⟩ ≤ β[0] =>
--     (β[0])
--   )
-- :]


-- -- expected: false 
-- -- RHS could be ⊥, but LHS must be > ⊥
-- #eval unify_decide [:
--   (∀ 1 :: ⟨even⟩ ≤ β[0] =>
--     (β[0])
--   )
-- :] [:
--   (∀ 1 => (β[0]))
-- :]

-- #eval unify_decide even [: ⊥ :]

-- -- expected: false 
-- -- RHS could be ⊤ -> @, but LHS must be > even -> @ 
-- -- must give negative positions ⊤, and positive positions ⊥
-- -- bound flips based on negative/positive position
-- #eval unify_decide [:
--   (∀ 1 :: β[0] ≤ ⟨even⟩ =>
--     (β[0] -> @)
--   )
-- :] [:
--   (∀ 1 => (β[0] -> @))
-- :]

-- -- expected: true 
-- #eval unify_decide [:
--   (∀ 1 :: β[0] ≤ ⟨nat_⟩ =>
--     (β[0] -> @)
--   )
-- :] [:
--   (∀ 1 :: β[0] ≤ ⟨even⟩ =>
--     (β[0] -> @)
--   )
-- :]

-- -- expected: false
-- #eval unify_decide [:
--   (∀ 1 :: β[0] ≤ ⟨even⟩ =>
--     (β[0] -> @)
--   )
-- :] [:
--   (∀ 1 :: β[0] ≤ ⟨nat_⟩ =>
--     (β[0] -> @)
--   )
-- :]

-- -- expected: true 
-- #eval unify_decide [:
--   (∃ 1 :: β[0] ≤ ⟨even⟩ =>
--     (β[0])
--   )
-- :] [:
--   (∃ 1 :: β[0] ≤ ⟨nat_⟩ =>
--     (β[0])
--   )
-- :]

-- -- expected: false 
-- #eval unify_decide [:
--   (∃ 2 :: β[0] × β[1] ≤ ⟨nat_⟩ × ⟨nat_⟩ =>
--     β[0] × β[1]
--   )
-- :] [:
--   (∃ 1 :: β[0] ≤ ⟨nat_⟩ =>
--     (succ*@ × β[0])
--   )
-- :]

-- -- expected: true 
-- #eval unify_decide [:
--   (∃ 1 :: β[0] ≤ ⟨even⟩ =>
--     (β[0])
--   )
-- :] nat_
-- #eval unify_decide [:
--   (∃ 1 =>
--     (β[0])
--   )
-- :] nat_

-- -- expected: false 
-- #eval unify_decide [:
--   (∃ 1 :: β[0] ≤ ⟨nat_⟩ =>
--     (β[0])
--   )
-- :] [:
--   (∃ 1 :: β[0] ≤ ⟨even⟩ =>
--     (β[0])
--   )
-- :]


-- -- expected: false
-- -- β[0] could be TOP
-- #eval unify_decide [:
--   (∃ 1 :: ⟨even⟩ ≤ β[0] =>
--     (β[0])
--   )
-- :] [:
--   (∃ 1 :: β[0] ≤ ⟨even⟩ =>
--     (β[0])
--   )
-- :]

-- #eval unify_decide [:
--   ⊤ 
-- :] [:
--   (∃ 1 :: β[0] ≤ ⟨even⟩ =>
--     (β[0])
--   )
-- :]




-- /-
-- first order quantification

-- μ NL .
--   {(0, [])} ∨ 
--   ∃ (n, l) : NL . 
--     (n + 1,  () :: l)  

-- ν N2L .
--   {0 => []} ∧ 
--   ∀ n -> l : N2L .  WRONG
--     {n + 1 => () :: l }

-- ν N2L .
--   0 -> nil*unit ∧ 
--   ∀ N2L ≤ N -> L .    
--     N + 1 => unit :: L

-- --- 
-- by second order quantification with subtyping rather than first order with membership,
-- we avoid mapping between terms and types in unification procedure.
-- We also enable the succient corecursive definitions of functions.

-- -/

-- /-
-- translating Liquid types into relational types

-- List with len where
-- [] : {v ∈ List | len v = 0} | 
-- () :: (xs : List) : {v ∈ List | len v = (len xs) + 1} | 

-- n : Nat -> {v ∈ List | len v = n}

-- ...

-- ∀ N . N ≤ Nat => N -> (∃ L . 
--   (N × L) ≤ (μ N' × L' .  (0 × []) | (N' + 1 × () :: L'))  =>
--   L
-- )

-- ...

-- ν N -> L .
--   0 -> [] ∧ 
--   N + 1 -> () :: L  
-- -/