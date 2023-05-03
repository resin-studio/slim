import Mathlib.Tactic.Basic
import Mathlib.Tactic.LeftRight


lemma v1 (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
(constructor;
  (intro h;
    cases h with 
      | intro hP hQR =>
        cases hQR with
          | inl hQ => 
            left; constructor;
              assumption;
              assumption
          | inr hR => 
            right; constructor;
                assumption;
              assumption
  );
  (intro h;
    cases h with
      | inl hPQ => 
        cases hPQ with 
          | intro hP hQ => 
            constructor;
              assumption;
              left; assumption
      | inr hPR =>
        cases hPR with
          | intro hP hR =>
            constructor;
              assumption;
              right; assumption
  )
)


#check Nat.lt
example (xs : List α) (h : xs.length = 1) : (0 < xs.length) :=
by simp [h];



lemma v2 (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
  ((Iff.intro
    ((λ h : P ∧ (Q ∨ R) =>
      (match h with
        | And.intro hP hQR => (match hQR with
            | Or.inl hQ => Or.inl (And.intro hP hQ : P ∧ Q)
            | Or.inr hR => Or.inr (And.intro hP hR : P ∧ R)
        )
      )
    ) : P ∧ (Q ∨ R) -> (P ∧ Q) ∨ (P ∧ R))
    ((λ h : P ∧ Q ∨ P ∧ R =>
      (And.intro 
        ((match h with
          | Or.inl (And.intro hP hQ) => hP
          | Or.inr (And.intro hP hR) => hP
        ) : P)
        ((match h with
          | Or.inl (And.intro hP hQ) => Or.inl hQ 
          | Or.inr (And.intro hP hR) => Or.inr hR
        ) : Q ∨ R)
      )
    ) : (P ∧ Q) ∨ (P ∧ R) -> P ∧ (Q ∨ R))
  ) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R))

class MyAdd (a : Type) where
  add : a -> a -> a

#check @MyAdd.add

instance : MyAdd Nat where
  add := Nat.add

instance : MyAdd Int where
  add := Int.add

instance : MyAdd Float where
  add := Float.add

def double [inst : Add a] (x : a) : a :=
  inst.add x x

#check @double
-- @double : {a : Type} → [inst : Add a] → a → a

-- #eval double 10
-- 20



#check Nat.ne_of_lt

example : ¬ 0 < 0 :=
  ((fun h => 
    let x := (Nat.ne_of_lt h)
    let y := (absurd rfl x)
    y
  ) : ¬ 0 < 0)

#check @absurd
example (n : Nat) (h : n ≠ 0) : .succ (.pred n) = n := 
  ((match n with
    | Nat.zero => absurd rfl h
    | Nat.succ m => rfl 
  ) : .succ (.pred n) = n)

example (n : Nat) (h : n ≠ 0) : .succ (.pred n) = n := by
  cases n with
  | zero =>
    -- goal: h : 0 ≠ 0 ⊢ succ (pred 0) = 0
    apply absurd rfl h
  | succ m =>
    -- second goal: h : succ m ≠ 0 ⊢ succ (pred (succ m)) = succ m
    rfl


-- induction with term and tactics
def add : Nat → Nat → Nat
  | m, .zero   => m
  | m, .succ n => .succ (add m n)

theorem add_zero (m : Nat)   : add m .zero = m := rfl
theorem add_succ (m n : Nat) : add m (.succ n) = .succ (add m n) := rfl

theorem zero_add : ∀ n, add .zero n = n
  | .zero   => rfl
  | .succ n => congrArg Nat.succ (zero_add n)

#check @congrArg
example : ∀ n, add .zero n = n := by
  (intro n;
    (induction n with
      | zero => apply rfl 
      | succ n IH => apply congrArg Nat.succ IH
    )
  )

theorem not_lt_zero (n : Nat) : ¬ n < 0 :=
  (fun h =>
    let h : n + 1 ≤ 0 := h 
    match n with
      | 0 =>
        let z := Nat.ne_of_lt h
        absurd rfl z
      | n' + 1 => 
        let IH := not_lt_zero n'
        let z : n' + 1 ≤ 0 := Nat.lt_of_succ_lt h 
        (IH z)
  )
