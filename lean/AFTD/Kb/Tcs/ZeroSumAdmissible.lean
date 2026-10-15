import AFTD.Prelude

/-!
# zero_sum_admissible

Topic: combinatorics   Node: b03efe7394ea

Provenance: formalization of a published result. Source: arXiv:2610.19965 (Proofs and disproofs of some conjectures on zero-sum problems), Sec. 1 (admissible sequences, following Sun's Definitions 1.2–1.3).

A sequence A of vectors in ℤ^r is admissible modulo n when no term is ≡ 0 (mod n).
-/

/-- Admissible modulo `n`: no term of `A` is `≡ 0 (mod n)`. -/
def zero_sum_admissible (n : ℕ) {r : ℕ} (A : List (Fin r → ℤ)) : Prop :=
  ∀ a ∈ A, ∃ j, ¬ (n : ℤ) ∣ a j
