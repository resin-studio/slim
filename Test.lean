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
