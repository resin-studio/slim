import TestLib
import ProgramLib

open Lean PersistentHashMap

def nat_ := [: 
  μ β[0] => zero*@ ∨ succ*β[0]
:]

#eval nat_

def even := [: 
  μ β[0] => zero*@ ∨ succ*succ*β[0]
:]


def weven := [: 
  μ β[0] => 
    zero*@ ∨ 
    succ*dumb*β[0]
:]


def nat_list := [: 
  μ β[0] => (
    (zero*@ × nil*@) ∨ 
    (∃ 2 :: β[0] × β[1] ≤ β[2] => 
      (succ*β[0] × cons*β[1]))
  )
:]

def even_list := [: 
  μ β[0] => (
    (zero*@ × nil*@) ∨ 
    (∃ 2 :: β[0] × β[1] ≤ β[2] => 
      (succ*succ*β[0] × cons*cons*β[1]))
  )
:]

-- def nat_to_list := [: 
--   ν β[0] => 
--     (zero*@ -> nil*@) ∧ 
--     (∀ 2 :: β[2] ≤ β[0] -> β[1] => 
--       succ*β[0] -> cons*β[1])
-- :]

def lte := [: 
  μ β[0] => 
    zero*@ × ⟨nat_⟩ ∨ 
    (∃ 2 :: β[0] × β[1] ≤ β[2] => 
      (succ*β[0] × succ*β[1]))
:]

def even_to_list := [: 
  ν β[0] => 
    (zero*@ -> nil*@) ∧ 
    (∀ 2 :: β[2] ≤ β[0] -> β[1] => 
      succ*succ*β[0] -> cons*cons*β[1])
:]

def plus := [: 
  μ β[0] => 
    (∃ 1 => 
      (x ~ zero*@ ∧ y ~ β[0] ∧ z ~ β[0])) ∨ 

    (∃ 3 :: (x ~ β[0] ∧ y ~ β[1] ∧ z ~ β[2]) ≤ β[3] => 
      (x ~ succ*β[0] ∧ y ~ β[1] ∧ z ~ succ*β[2]))
:]

-- #eval unify_decide 0 weven nat_ -- == false
-- #eval unify_decide 0 even nat_ -- == true 
-- #eval unify_decide 0 nat_ even -- == false


-- #eval unify_decide 0 
-- [: (∀ 1 :: β[0] ≤ ⟨nat_⟩ => β[0] -> β[0]) :]
-- [: ⟨nat_⟩ -> ⟨nat_⟩ :]
-- -- == true 

-- #eval unify_decide 0 
-- [: ⟨nat_⟩ -> ⟨nat_⟩ :]
-- [: (∀ 1 :: β[0] ≤ ⟨nat_⟩ => β[0] -> β[0]) :]
-- -- == false 

-- #eval unify_decide 0
-- [: ∃ 2 :: β[0] ≤ ⟨even⟩ => β[0] × β[1]:] 
-- [: ∃ 2 :: β[0] ≤ ⟨nat_⟩ => β[0] × β[1]:] 
-- -- == true

-- #eval unify_decide 0 
-- [: ∃ 2 :: ⟨even⟩ ≤ β[0] => β[0] × β[1]:] 
-- [: ∃ 2 :: ⟨nat_⟩ ≤ β[0] => β[0] × β[1]:] 
-- -- == false

-- #eval unify_decide 0 
-- [: ∃ 2 :: β[0] ≤ ⟨nat_⟩ => β[0] × β[1]:] 
-- [: ∃ 2 :: β[0] ≤ ⟨even⟩ => β[0] × β[1]:] 
-- -- == false

-- #eval unify_decide 0 
-- [: ∃ 2 :: ⟨nat_⟩ ≤ β[0] => β[0] × β[1]:] 
-- [: ∃ 2 :: ⟨even⟩ ≤ β[0] => β[0] × β[1]:] 
-- -- == true

-- #eval unify_decide 0 
-- [: (zero*@) :] nat_ 
-- -- == true

-- #eval unify_decide 0 
-- [: (succ*(zero*@)) :] nat_ 
-- -- == true

-- #eval unify_decide 0 
-- [: ∀ 1 => (succ*(β[0])) :] 
-- nat_ 
-- -- == true

-- #eval unify_decide 0 
-- [: ∃ 1 => (succ*(β[0])) :] 
-- nat_ 
-- -- == false 


-- #eval unify_reduce 0 
-- [: (succ*(α[0])) :] 
-- nat_ 
-- [: α[0] :]
-- -- == [: (μ β[0] => (zero*@ ∨ succ*β[0])) :]

-- #eval unify_decide 0 
--   even
--   nat_

#eval unify_decide 0 
  even_list
  nat_list
-- == true

#eval unify_decide 0 
  nat_list
  even_list
-- == false 

-- #eval unify_decide 0 
-- [: 
--   μ β[0] => (
--     (zero*@ × nil*@) ∨ 
--     (∃ 2 :: β[0] × β[1] ≤ β[2] => 
--       (succ*succ*β[0] × cons*cons*β[1]))
--   )
-- :]
-- [: 
--   μ β[0] => (
--     (zero*@ × nil*@) ∨ 
--     (∃ 2 :: β[0] × β[1] ≤ β[2] => 
--       (succ*β[0] × cons*β[1]))
--   )
-- :]

-- #eval unify_decide 0 
--   nat_list
--   even_list
-- -- == false


-- #eval unify_decide 0 
--   [: (zero*@ × nil*@) :] 
--   nat_list
-- -- == true

-- #eval unify_decide 0 
--   [: zero*@ × dumb*@ :] 
--   nat_list
-- -- == false

-- -- this is record type is not wellformed 
-- #eval unify_decide 2 
--   [: α[0] × α[1] :] 
--   nat_list
-- -- == false


-- #eval unify_reduce 1
--   [: zero*@ × α[0] :] 
--   nat_list
--   [: α[0] :]
-- -- == [: nil*@ :]

-- #eval unify_reduce 1
--   [: (succ*succ*zero*@ × cons*α[0]) :] 
--   nat_list
--   [: α[0]:]
-- -- == [: cons*nil*@ :]


-- #eval unify_decide 1 
--   [: (succ*zero*@ × cons*cons*α[0]) :] 
--   nat_list
-- -- == false


-- #eval unify_decide 0 
--   nat_to_list
--   [: (succ*zero*@) -> (cons*nil*@) :] 
-- -- == true

-- #eval unify_reduce 1
--   nat_to_list
--   [: (succ*zero*@ -> cons*α[0]) :] 
--   [: α[0] :]
-- -- == [: nil*@ :]

-- #eval unify_decide 1
--   nat_to_list
--   [: (succ*zero*@ -> cons*cons*α[0]) :] 
-- -- == false

-- #eval unify_reduce 1 
-- [:
--     x ~ zero*@ ∧ 
--     y ~ α[0] ∧ 
--     z ~ zero*@
-- :] plus [: α[0] :]
-- -- == [: zero*@ :]


-- #eval unify_reduce 1 [:
--   (
--     x ~ (succ*zero*@) ∧ 
--     y ~ (succ*zero*@) ∧ 
--     z ~ (α[0])
--   )
-- :] plus [: α[0] :]
-- -- == [: succ*succ*zero*@ :]


-- #eval unify_reduce 1 [:
--   (
--     x ~ (succ*succ*zero*@) ∧ 
--     y ~ (succ*zero*@) ∧
--     z ~ (α[0])
--   )
-- :] plus
-- [: α[0] :]
-- -- == [: succ*succ*succ*zero*@ :]

-- #eval unify_reduce  1 [:
--   (
--     x ~ (succ*zero*@) ∧ 
--     y ~ (α[0]) ∧
--     z ~ (succ*succ*zero*@)
--   )
-- :] plus
-- [: α[0] :]
-- -- == [: succ*zero*@ :]



-- -- expected: α[0] ↦ succ*zero*@
-- #eval unify_reduce 1 [:
-- (
--   x ~ α[0] ∧
--   y ~ succ*zero*@ ∧
--   z ~ succ*succ*zero*@
-- )
-- :] plus
-- [: α[0] :]
-- -- == [: succ*zero*@ :]


-- #eval unify_reduce 2 [:
-- (
--   x ~ (α[0]) ∧
--   y ~ (α[1]) ∧
--   z ~ (succ*succ*zero*@)
-- )
-- :] plus
-- [: x ~ α[0] ∧ y ~ α[1] :]
-- -- == [:
-- -- (
-- --   (x ~ succ*succ*zero*@ ∧ y ~ zero*@) ∨
-- --   (x ~ succ*zero*@ ∧ y ~ succ*zero*@) ∨ 
-- --   (x ~ zero*@ ∧ y ~ succ*succ*zero*@)
-- -- )
-- -- :]

-- #eval unify_reduce 2 [:
-- (
--   x ~ (succ*succ*zero*@) ∧
--   y ~ (α[1]) ∧
--   z ~ (α[0])
-- )
-- :] plus
-- [: y ~ α[1] ∧ z ~ α[0] :]
-- -- == [: (y ~ α[1] ∧ z ~ succ*succ*α[1]) :]

-- #eval infer_reduce 1 [:
--   let y[0] : (hello*@ -> α[0]) = (λ y[0] => y[0]) =>
--   y[0]
-- :]
-- -- == [: hello*@ -> hello*@ :]

-- #eval unify_reduce 1 
-- [: α[0] -> α[0] :]
-- [: (hello*@ -> α[0]) :]
-- [: α[0] :]
-- -- == [: hello*@ :]



-- def test_unify_tags : IO Unit :=
--   test "unify tags" [
--     ("same", unify_decide 0 [: zero * @ :] [: zero * @ :] == true),
--     ("diff", unify_decide 0 [: zero * @ :] [: one * @ :] == false)
--   ]


-- def test_introduction : IO Unit :=
--   test "introduction" [
--     ("hello world", 
--       infer_reduce 0 
--       [: (hello;(), world;()) :]
--       ==
--       [: (hello*@ × world*@) :]
--     )
--   ]

-- def test_elimination : IO Unit :=
--   test "elimination" [
--     ("1", 
--       infer_reduce 0 
--       [: ((λ y[0] => y[0]) zero;()) :]
--       ==
--       [: zero*@ :]
--     )
--   ]


-- def test_generalization : IO Unit :=
--   test "generalization" [
--     ("annotated", 
--       infer_reduce 1 [:
--         let y[0] : str*@ -> ⊤ = (λ y[0] => hello ; y[0]) =>
--         y[0]
--       :]
--       == 
--       [: (str*@ -> hello*str*@) :]
--     ),
--     ("existentially annotated", 
--       infer_reduce 1 [:
--         let y[0] : ∃ 1 => β[0] = (λ y[0] => hello ; y[0]) =>
--         y[0]
--       :]
--       == 
--       [: (∀ 1 => (β[0] -> hello*β[0])) :]
--     ),
--     ("universally annotated", 
--       infer_reduce 1 [:
--         let y[0] : ∀ 2 => β[0] -> β[1] = (λ y[0] => hello ; y[0]) =>
--         y[0]
--       :]
--       == 
--       [: (∀ 1 => (β[0] -> hello*β[0])) :]
--     ),
--     ("unannotated", 
--       infer_reduce 0 [:
--         let y[0] = (λ y[0] => hello ; y[0]) =>
--         (
--           y[0]
--         )
--       :]
--       == 
--       [: (∀ 1 => (β[0] -> hello*β[0])) :]
--     ),
--     ("nested scopes 1", 
--       infer_reduce 0 [:
--         (λ y[0] => 
--           let y[0] = (λ y[0] => (y[1], (hello ; y[0]))) =>
--           (
--             y[0]
--           )
--         )
--       :]
--       == 
--       [: (∀ 1 => (β[0] -> (∀ 1 => (β[0] -> (β[1] × hello*β[0]))))) :]
--     ),

--     ("nested scopes 2", 
--       infer_reduce 0 [:
--         (λ y[0] => 
--           let y[0] = (λ y[0] => y[0]) =>
--           let y[0] = (λ y[0] => ((y[1] y[2]), (hello ; y[0]))) =>
--           (
--             y[0]
--           )
--         )
--       :]
--       == 
--       [: (∀ 1 => (β[0] -> (∀ 1 => (β[0] -> (β[1] × hello*β[0]))))) :]
--     )
--   ]


-- def test_widening : IO Unit :=
--   test "widening" [
--     ("1", 
--       infer_reduce 0 [:
--         let y[0] : ∀ 1 => β[0] -> (β[0] -> (β[0] × β[0])) = _ => 
--         (y[0] hello;())
--       :]
--       == 
--       [: (∀ 1 => ((hello*@ ∨ β[0]) -> ((hello*@ ∨ β[0]) × (hello*@ ∨ β[0])))) :]
--     ),
--     ("2", 
--       infer_reduce 0 [:
--         let y[0] : ∀ 1 => β[0] -> (β[0] -> (β[0] × β[0])) = _ => 
--         ((y[0] hello;()) world;())
--       :]
--       ==
--       [: ((hello*@ ∨ world*@) × (hello*@ ∨ world*@)) :]
--     )
--   ]

      #eval infer_reduce 0 [:
        let y[0] : ∀ 1 => β[0] -> (β[0] -> (β[0] × β[0])) = _ => 
        (y[0] hello;())
      :]

      #eval infer_reduce 0 [:
        let y[0] : ∀ 1 => β[0] -> (β[0] -> (β[0] × β[0])) = _ => 
        ((y[0] hello;()) world;())
      :]

-- def test_narrowing : IO Unit :=
--   test "narrowing" [
--     ("1", 
--       infer_reduce 0 [:
--         let y[0] : uno*@ -> @ = _ => 
--         (λ y[0] =>
--           ((y[1] y[0])))
--       :]
--       ==
--       [: (uno*@ -> @) :]
--     ),
--     ("2",
--       infer_reduce 0 [:
--         let y[0] : uno*@ -> @ = _ => 
--         let y[0] : dos*@ -> @ = _ =>
--         (λ y[0] =>
--           ((y[2] y[0]), (y[1] y[0])))
--       :]
--       ==
--       [: (((uno*@ ∧ dos*@) -> (@ × @)) ∨ ((dos*@ ∧ uno*@) -> (@ × @))) :]
--     )
--   ]

-- def main : IO Unit := do
--   test_unify_tags
--   test_introduction
--   test_generalization
--   test_widening
--   test_narrowing

-- ------------------------------------------------------------


-- -- -- term testing
-- -- #eval [:
-- --   λ[ 
-- --     for y[0] : α[0] => y[0],
-- --     for y[0] : α[0] => y[0] 
-- --   ]
-- -- :]

-- -- #eval [:
-- --   ω[ 
-- --     left := x[0],
-- --     right := x[0]
-- --   ]
-- -- :]


-- -- #eval [:
-- --   succ;zero;()
-- -- :]



-- -- #eval infer_reduce 0 [:
-- --   succ;zero;()
-- -- :]

-- -- #eval [:
-- --   succ;zero;()
-- -- :]

-- -- #eval [:
-- --   x[0]/hello
-- -- :]

-- -- #eval infer_reduce 0 [:
-- --   _ 
-- -- :]


-- -- #eval [:
-- --   α[0] + α[1]
-- -- :]

-- -- #eval [:
-- --   α[0] × α[1]
-- -- :]

-- -- #eval [:
-- --   (x[0], x[1])
-- -- :]


-- -- #eval infer_reduce 0 [:
-- --   λ [for y[0] => y[0]]
-- -- :]

-- -- #eval infer_reduce 0 [:
-- --   λ [for y[0] : abc*@ => y[0]]
-- -- :]

-- -- #eval infer_reduce 0 [:
-- --   λ [for y[0] : inp*@ -> out*@ =>
-- --   Out ; λ [for y[0] => 
-- --       cons ; ((y[1] y[0]), nil ; ())
-- --   ]
-- --   ]
-- -- :]

-- -- #eval infer_reduce 0 [:
-- --   ((), nil ; ())
-- -- :]

  
-- -- #eval [:
-- --   hello*thing~@
  
-- -- :]

-- -- -----



-- -- def repli := [:
-- --   ∀ 1 => β[0] -> (ν β[0] =>
-- --     (zero*@ -> nil*@) ∧
-- --     (∀ 2 :: β[2] ≤ (β[0] -> β[1]) =>
-- --       succ*β[0] -> cons*(β[3] × β[1])
-- --     )
-- --   )
-- -- :]


-- -- -----

-- -- #eval unify_decide 0 
-- -- [: uno ~ @ ∧ dos ~ @ ∧ tres ~ @:]
-- -- [: uno ~ @ ∧ tres ~ @:]

-- -- #eval unify_decide 0 
-- -- [: uno ~ @ ∧ dos ~ @ ∧ tres ~ @:]
-- -- [: ∀ 1 :: β[0] ≤ uno ~ @ ∨ dos ~ @ ∨ tres ~ @ => β[0]:]

-- -- #eval unify_decide 0 
-- -- [: ∀ 1 :: β[0] ≤ uno ~ @ ∨ dos ~ @ ∨ tres ~ @ => β[0]:]
-- -- [: uno ~ @ ∧ dos ~ @ ∧ tres ~ @:]


-- -- #eval unify_decide 0 
-- -- [: uno ~ @ ∨ dos ~ @ ∨ tres ~ @ :]
-- -- [:dos ~ @ ∧ tres ~ @ :]

-- -- #eval unify_decide 0 
-- -- [:dos ~ @ ∧ tres ~ @ ∧ four ~ @:]
-- -- [: uno ~ @ ∨ dos ~ @ ∨ tres ~ @ :]

-- -- #eval unify_decide 0 
-- -- [: ∀ 1 :: β[0] ≤ uno ~ @ ∨ dos ~ @ ∨ tres ~ @ => β[0]:]
-- -- [:dos ~ @ ∧ tres ~ @ ∧ four ~ @:]

-- -- #eval unify_decide 0 
-- -- [: ∀ 1 :: uno ~ @ ∧ dos ~ @ ∧ tres ~ @ ≤ β[0] => β[0]:]
-- -- [:dos ~ @ ∧ tres ~ @ :]

-- -- #eval unify_decide 0 
-- -- [: ∀ 1 :: uno ~ @ ∧ dos ~ @ ∧ tres ~ @ ≤ β[0] => β[0]:]
-- -- [: ∀ 1 :: uno ~ @ ∧ dos ~ @ ≤ β[0] => β[0]:]

-- -- #eval unify_decide 0 
-- -- [: ∀ 1 :: uno ~ @ ∧ dos ~ @ ≤ β[0] => β[0]:]
-- -- [: ∀ 1 :: uno ~ @ ∧ dos ~ @ ∧ tres ~ @ ≤ β[0] => β[0]:]

-- -- #eval unify_decide 0 
-- -- [: ∀ 1 :: β[0] ≤ ⟨even⟩ => hello * β[0] :]
-- -- [: ∀ 1 :: β[0] ≤ ⟨nat_⟩ => hello * β[0] :]

-- -- #eval unify_decide 0 
-- -- [: ∀ 1 :: β[0] ≤ ⟨nat_⟩ => hello * β[0] :]
-- -- [: ∀ 1 :: β[0] ≤ ⟨even⟩ => hello * β[0] :]

-- -- #eval unify_decide 0 
-- -- [: ∀ 1 :: uno ~ @ ∧ dos ~ @ ∧ tres ~ @ ≤ β[0] => β[0]:]
-- -- [: ∀ 1 :: uno ~ @ ∧ dos ~ @ ∧ four ~ @ ≤ β[0] => β[0]:]

-- -- #eval unify_decide 0 
-- -- [: ∀ 1 :: β[0] ≤ uno ~ @ => β[0]:]
-- -- [:uno ~ @ ∧ four ~ @:]

-- -- #eval unify_decide 0 
-- -- [: ∀ 1 :: uno ~ @ ≤ β[0] => β[0]:]
-- -- [:uno ~ @ ∧ four ~ @:]


-- -- ----- 

def nat_to_unit := [: 
  ν β[0] => 
    (zero*@ -> @) ∧ 
    (∀ 1 :: β[1] ≤ β[0] -> @ => 
      (succ*β[0]) -> @) 
:]

def even_to_unit := [: 
  ν β[0] => 
    (zero*@ -> @) ∧ 
    (∀ 1 :: β[1] ≤ β[0] -> @ => 
      (succ*succ*β[0]) -> @)
:]

-- -- #eval unify_decide 0 
-- -- nat_to_unit
-- -- [: (zero*@ -> @) :]

-- -- #eval unify_decide 0 
-- -- nat_to_unit
-- -- nat_to_unit

-- -- #eval unify_decide 0 
-- -- nat_to_unit
-- -- [: (succ*zero*@ -> @) :]

-- -- #eval unify_decide 0 
-- -- even_to_unit
-- -- [: (succ*succ*zero*@ -> @) :]

-- -- #eval unify_decide 0 
-- -- even_to_unit
-- -- [: (succ*zero*@ -> @) :]

-- -- limitation: can't unify this
-- #eval unify_decide 5
-- [: (⟨even⟩ × α[0]) :]
-- [: ⟨nat_list⟩ :]
-- -- false

-- #eval unify_decide 5
-- [: ∀ 1 :: β[0] ≤ ⟨even⟩ => β[0] -> @ :]
-- [: ∀ 1 :: β[0] ≤ ⟨even⟩ => β[0] -> @ :]

-- #eval unify_decide 5
-- [: ∀ 1 :: β[0] ≤ ⟨nat_⟩ => β[0] -> @ :]
-- [: ∀ 1 :: β[0] ≤ ⟨even⟩ => β[0] -> @ :]

-- #eval unify_decide 5
-- [: ∀ 1 :: β[0] ≤ ⟨even⟩ => β[0] -> @ :]
-- [: ∀ 1 :: β[0] ≤ ⟨nat_⟩ => β[0] -> @ :]



#eval unify_decide 5
nat_to_unit
even_to_unit
-- == true

#eval unify_decide 5
even_to_unit
nat_to_unit
-- == false


#eval infer_reduce 5 [:
  (λ y[0] => λ[
  for zero;() => nil;(),
  for succ;y[0] => cons;(y[1] y[0])
  ]) 
:]

-- TODO: figure out why this fails
#eval infer_reduce 0 [:
  fix(λ y[0] => λ[
  for zero;() => nil;(),
  for succ;y[0] => cons;(y[1] y[0])
  ])
:]



-- expected: false 
-- this is overly strict, but safe 
-- there is no way for the LHS to know to instantiate with ⊥ vs nat_
#eval unify_decide 0 [:
  (∀ 1 :: β[0] ≤ ⟨even⟩ =>
    (β[0])
  )
:] [:
  (∀ 1 :: β[0] ≤ ⟨nat_⟩ =>
    (β[0])
  )
:]

-- expected: true 
#eval unify_decide 0 [:
  (∀ 1 :: ⟨even⟩ ≤ β[0] =>
    (β[0])
  )
:] [:
  (∀ 1 :: ⟨nat_⟩ ≤ β[0] =>
    (β[0])
  )
:]


-- TODO
-- expected: false 
-- RHS could be ⊥, but LHS must be > ⊥
#eval unify_decide 0 [:
  (∀ 1 :: ⟨even⟩ ≤ β[0] =>
    (β[0])
  )
:] [:
  (∀ 1 => (β[0]))
:]

-- TODO
-- expected: false 
-- RHS could be ⊤ -> @, but LHS must be > even -> @ 
-- must give negative positions ⊤, and positive positions ⊥
-- bound flips based on negative/positive position
#eval unify_decide 0 [:
  (∀ 1 :: β[0] ≤ ⟨even⟩ =>
    (β[0] -> @)
  )
:] [:
  (∀ 1 => (β[0] -> @))
:]

-- expected: true 
#eval unify_decide 0 [:
  (∀ 1 :: β[0] ≤ ⟨nat_⟩ =>
    (β[0] -> @)
  )
:] [:
  (∀ 1 :: β[0] ≤ ⟨even⟩ =>
    (β[0] -> @)
  )
:]

-- expected: false
#eval unify_decide 0 [:
  (∀ 1 :: β[0] ≤ ⟨even⟩ =>
    (β[0] -> @)
  )
:] [:
  (∀ 1 :: β[0] ≤ ⟨nat_⟩ =>
    (β[0] -> @)
  )
:]

-- expected: true 
#eval unify_decide 0 [:
  (∃ 1 :: β[0] ≤ ⟨even⟩ =>
    (β[0])
  )
:] [:
  (∃ 1 :: β[0] ≤ ⟨nat_⟩ =>
    (β[0])
  )
:]

-- TODO
-- expected: false 
#eval unify_decide 0 [:
  (∃ 2 :: β[0] × β[1] ≤ ⟨nat_⟩ × ⟨nat_⟩ =>
    β[0] × β[1]
  )
:] [:
  (∃ 1 :: β[0] ≤ ⟨nat_⟩ =>
    (succ*@ × β[0])
  )
:]

-- expected: true 
#eval unify_decide 0 [:
  (∃ 1 :: β[0] ≤ ⟨even⟩ =>
    (β[0])
  )
:] nat_
#eval unify_decide 0 [:
  (∃ 1 =>
    (β[0])
  )
:] nat_

-- expected: false 
#eval unify_decide 0 [:
  (∃ 1 :: β[0] ≤ ⟨nat_⟩ =>
    (β[0])
  )
:] [:
  (∃ 1 :: β[0] ≤ ⟨even⟩ =>
    (β[0])
  )
:]


-- TODO
-- expected: false
-- β[0] could be TOP
#eval unify_decide 0 [:
  (∃ 1 :: ⟨even⟩ ≤ β[0] =>
    (β[0])
  )
:] [:
  (∃ 1 :: β[0] ≤ ⟨even⟩ =>
    (β[0])
  )
:]

-- expected: false
#eval unify_decide 0 [:
  ⊤ 
:] [:
  (∃ 1 :: β[0] ≤ ⟨even⟩ =>
    (β[0])
  )
:]




-- -- /-
-- -- first order quantification

-- -- μ NL .
-- --   {(0, [])} ∨ 
-- --   ∃ (n, l) : NL . 
-- --     (n + 1,  () :: l)  

-- -- ν N2L .
-- --   {0 => []} ∧ 
-- --   ∀ n -> l : N2L .  WRONG
-- --     {n + 1 => () :: l }

-- -- ν N2L .
-- --   0 -> nil*unit ∧ 
-- --   ∀ N2L ≤ N -> L .    
-- --     N + 1 => unit :: L

-- -- --- 
-- -- by second order quantification with subtyping rather than first order with membership,
-- -- we avoid mapping between terms and types in unification procedure.
-- -- We also enable the succient corecursive definitions of functions.

-- -- -/

-- -- /-
-- -- translating Liquid types into relational types

-- -- List with len where
-- -- [] : {v ∈ List | len v = 0} | 
-- -- () :: (xs : List) : {v ∈ List | len v = (len xs) + 1} | 

-- -- n : Nat -> {v ∈ List | len v = n}

-- -- ...

-- -- ∀ N . N ≤ Nat => N -> (∃ L . 
-- --   (N × L) ≤ (μ N' × L' .  (0 × []) | (N' + 1 × () :: L'))  =>
-- --   L
-- -- )

-- -- ...

-- -- ν N -> L .
-- --   0 -> [] ∧ 
-- --   N + 1 -> () :: L  
-- -- -/

-- -- #eval [: β[0] :]
-- -- #eval [: β[0] :]

-- -- #check [: β[0] ∨ α[0] :]
-- -- #check [: β[0] ∧ α[0] :]
-- -- #check [: β[0] × α[0] :]
-- -- #check [: β[0] + α[0] :]
-- -- def x := 0
-- -- #check [: ∀ 1 :: β[0] ≤ α[0] => β[⟨x⟩] :]
-- -- #check [: ∀ 1 :: β[0] ≤ α[0] => β[0] :]
-- -- #check [: ∀ 2 :: α[0] ≤ α[0] => β[0] :]
-- -- #check [: ∀ 2 => β[0] :]
-- -- #check [: @ :]
-- -- #check [: α[24] :]
-- -- #check [: foo * @ :]
-- -- #check [: foo * @ ∨ (boo * @) :]
-- -- #check [: μ β[0] => foo * @ :]
-- -- #check [: foo * boo * @ :]
-- -- #check [: μ β[0] => foo * boo * @ :]
-- -- #check [: μ β[0] => foo * β[0] :]
-- -- #check [: μ β[0] => foo * β[0] ∧ α[0] ∨ α[2] ∧ α[0]:]
-- -- #check [: β[3] ∧ α[0] -> α[1] ∨ α[2] :]
-- -- #check [: μ β[0] => foo * β[0] ∧ α[0] ∨ α[2] ∧ α[0] -> α[1] ∨ α[2] :]
-- -- #check [: μ β[0] => foo * β[0] ∧ α[0] ∨ α[2] ∧ α[0] :]
-- -- #check [: α[0] :]

-- -- #eval [: ∀ 2 :: α[0] ≤ α[0] => β[0] :]
-- -- #eval [: μ β[0] => foo * β[0] ∧ α[0] ∨ α[2] ∧ α[0] :]



-- -- #eval ({} : PHashMap Nat Ty)

-- -- def zero_ := [: 
-- --     zero * @
-- -- :]

#eval [:
  let y[0] : (
    (zero*@ -> nil*@) ∧
    (succ*zero*@ -> cons*nil*@) ∧
    (succ*succ*zero*@ -> cons*cons*nil*@)
  ) = _ => 
  y[0]
:]

#eval synth_reduce [:
  let y[0] : (
    (zero*@ -> nil*@) ∧
    (succ*zero*@ -> cons*nil*@) ∧
    (succ*succ*zero*@ -> cons*cons*nil*@)
  ) = _ => 
  y[0]
:]

#eval synth_reduce [:
  let y[0] : (∀ 1 => β[0] -> (ν β[0] =>
    (zero*@ -> nil*@) ∧
    (∀ 2 :: β[2] ≤ (β[0] -> β[1]) =>
      succ*β[0] -> cons*(β[3] × β[1])
    )
  )) = _ => 
  y[0]
:]