import AFTD.Prelude

/-!
# normalized_tree_rank_partial_mixture

Topic: combinatorics   Node: bf7aa2aeb03a

Provenance: helper lemma. A sequence invariant considered for the rooted recurrence in OP-1399.

Normalized sequences with the first three ranks of a particular 19-vertex rooted tree, binomial bounds, likelihood order, bounded-mixture and difference log-concavity, and full partial synchronization.
-/

def normalized_tree_rank_partial_mixture (u a : ℕ → ℝ) : Prop := a 0 = 1 ∧ u 0 = 1 ∧ a 1 = 18 / 19 ∧ u 1 = 1 ∧ u 2 = 56 / 57 ∧ a 2 = 47 / 57 ∧ (∀ k, 0 ≤ a k ∧ a k ≤ u k ∧ u k ≤ 1) ∧ (∀ k, 6 < k → a k = 0 ∧ u k = 0) ∧ (∀ i j, i < j → a j * (u i - a i) ≤ a i * (u j - a j)) ∧ (∀ k, (u k - a k) * (u (k + 2) - a (k + 2)) ≤ (u (k + 1) - a (k + 1)) ^ 2) ∧ (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ k, (a k + t * (u k - a k)) * (a (k + 2) + t * (u (k + 2) - a (k + 2))) ≤ (a (k + 1) + t * (u (k + 1) - a (k + 1))) ^ 2) ∧ (∀ i j, 1 ≤ j → j ≤ i → a (i + 1) * u (j - 1) + a (j - 1) * u (i + 1) ≤ a i * u j + a j * u i)
