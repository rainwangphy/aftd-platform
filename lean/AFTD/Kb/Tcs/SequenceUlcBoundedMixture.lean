import AFTD.Prelude

/-!
# sequence_ulc_bounded_mixture

Topic: combinatorics   Node: 712cbe3d3d58

Provenance: helper lemma. Notation for a discarded analytic route to OP-1399; compare arXiv:0707.2340, Sections 6–7.

The two nonnegative sequences have normalized initial terms, bounded and downward-closed supports, binomial upper bounds, likelihood order, and ultra-log-concavity of every mixture a+t c for zero at most t at most one.
-/

def sequence_ulc_bounded_mixture (n : ℕ) (a c : ℕ → ℝ) : Prop :=
  a 0 = 1 ∧ c 0 = 0 ∧
  (∀ k, 0 ≤ a k ∧ 0 ≤ c k ∧ a k + c k ≤ (Nat.choose n k : ℝ)) ∧
  (∀ k, n < k → a k = 0 ∧ c k = 0) ∧
  (∀ i j, i ≤ j → 0 < a j → 0 < a i) ∧
  (∀ i j, i ≤ j → 0 < a j + c j → 0 < a i + c i) ∧
  (∀ i j, i < j → a j * c i ≤ a i * c j) ∧
  (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ k : ℕ, k + 2 ≤ n →
    (a k + t * c k) * (a (k + 2) + t * c (k + 2)) *
      (Nat.choose n (k + 1) : ℝ) ^ 2 ≤
    (a (k + 1) + t * c (k + 1)) ^ 2 *
      (Nat.choose n k : ℝ) * (Nat.choose n (k + 2) : ℝ))
