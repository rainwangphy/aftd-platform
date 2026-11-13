import AFTD.Prelude

/-!
# normalized_binary_tree_prefix_input

Topic: combinatorics   Node: 9e7ca18f1ac9

Provenance: helper lemma. A tested sequence invariant related to OP-1399.

The normalized sequences have specified first three ranks, bounded support, likelihood order, log-concavity of every bounded mixture, and full partial synchronization.
-/

def normalized_binary_tree_prefix_input (u a : ℕ → ℝ) : Prop :=
  a 0 = 1 ∧ u 0 = 1 ∧ a 1 = 4 / 5 ∧ u 1 = 1 ∧ u 2 = 476 / 495 ∧ a 2 = 316 / 495 ∧
  (∀ k, 0 ≤ a k ∧ a k ≤ u k ∧ u k ≤ 1) ∧
  (∀ k, 6 < k → a k = 0 ∧ u k = 0) ∧
  (∀ i j, i < j → a j * (u i - a i) ≤ a i * (u j - a j)) ∧
  (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ k,
    (a k + t * (u k - a k)) * (a (k + 2) + t * (u (k + 2) - a (k + 2))) ≤
      (a (k + 1) + t * (u (k + 1) - a (k + 1))) ^ 2) ∧
  (∀ i j, 1 ≤ j → j ≤ i →
    a (i + 1) * u (j - 1) + a (j - 1) * u (i + 1) ≤ a i * u j + a j * u i)
