import AFTD.Prelude

/-!
# is_valid_consecutive_sum_seq

Topic: combinatorics   Node: e9aa6fe8f3c0

Provenance: formalization of a published result. Source: arXiv:2611.30462 Section 3

A sequence s of integers of length n ≥ 1 starting at s(1) = a is valid with step bound K if it is strictly increasing with adjacent differences at most K and has pairwise distinct consecutive sums.
-/

/-- Predicate that s is a valid sequence of length n starting at a with differences at most K and distinct consecutive sums. -/
def is_valid_consecutive_sum_seq (a K : ℤ) (n : ℕ) (s : ℕ → ℤ) : Prop :=
  1 ≤ n ∧
  s 1 = a ∧
  (∀ i ∈ Finset.Ico 1 n, s i < s (i + 1) ∧ s (i + 1) - s i ≤ K) ∧
  ∀ u r v s_len : ℕ, u + r ≤ n → v + s_len ≤ n → 0 < r → 0 < s_len →
    (∑ i ∈ Finset.Ioc u (u + r), s i = ∑ j ∈ Finset.Ioc v (v + s_len), s j) →
      u = v ∧ r = s_len
