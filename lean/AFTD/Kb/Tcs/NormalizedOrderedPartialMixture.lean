import AFTD.Prelude

/-!
# normalized_ordered_partial_mixture

Topic: combinatorics   Node: 5332bfee4556

Provenance: helper lemma. A sequence invariant considered for the rooted recurrence in OP-1399.

The normalized input sequences have initial values one, binomial rank bounds, support through rank six, likelihood order, log-concavity of the difference and every bounded mixture, and full partial synchronization.
-/

def normalized_ordered_partial_mixture (u a : ℕ → ℝ) : Prop := a 0 = 1 ∧ u 0 = 1 ∧ a 1 = 1 ∧ u 1 = 1 ∧ (∀ k, 0 ≤ a k ∧ a k ≤ u k ∧ u k ≤ 1) ∧ (∀ k, 6 < k → a k = 0 ∧ u k = 0) ∧ (∀ i j, i < j → a j * (u i - a i) ≤ a i * (u j - a j)) ∧ (∀ k, (u k - a k) * (u (k + 2) - a (k + 2)) ≤ (u (k + 1) - a (k + 1)) ^ 2) ∧ (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ k, (a k + t * (u k - a k)) * (a (k + 2) + t * (u (k + 2) - a (k + 2))) ≤ (a (k + 1) + t * (u (k + 1) - a (k + 1))) ^ 2) ∧ (∀ i j, 1 ≤ j → j ≤ i → a (i + 1) * u (j - 1) + a (j - 1) * u (i + 1) ≤ a i * u j + a j * u i)
