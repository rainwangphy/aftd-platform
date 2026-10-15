import AFTD.Prelude

/-!
# zero_sum_good_subseq

Topic: combinatorics   Node: 5b1d6bf300b3

Provenance: formalization of a published result. Source: arXiv:2610.19965 (Proofs and disproofs of some conjectures on zero-sum problems), condition (1.2).

A nonempty set I of positions of A is good when Σ_{i∈I} a_i ≡ 0 (mod n) but Σ_{i∈I} a_i ≢ 0 (mod n²) (condition (1.2)).
-/

/-- Positions `I` whose sum is `≡ 0 (mod n)` but `≢ 0 (mod n²)`. -/
def zero_sum_good_subseq (n : ℕ) {r : ℕ} (A : List (Fin r → ℤ)) (I : Finset (Fin A.length)) : Prop :=
  I.Nonempty ∧ (∀ j, (n : ℤ) ∣ ∑ i ∈ I, A.get i j) ∧ ∃ j, ¬ ((n : ℤ) ^ 2 ∣ ∑ i ∈ I, A.get i j)
