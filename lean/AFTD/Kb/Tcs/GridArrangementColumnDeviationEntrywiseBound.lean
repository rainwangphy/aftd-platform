import AFTD.Prelude
import AFTD.Kb.Tcs.GridArrangementColumnDeviationSubsetSumBound

/-!
# grid_arrangement_column_deviation_entrywise_bound

Topic: combinatorics   Node: af3278d57a1f

Provenance: formalization of a published result. Source: arXiv:2610.38386 Lemma 3.8

For any grid arrangement $S$ of order $n \ge 3$ and any column index $j$, the column deviation satisfies $|\gamma_j| \le n^2(n-1)/2$.
-/

/-- Individual column-deviation bound for an order-$n$ grid arrangement. -/
theorem grid_arrangement_column_deviation_entrywise_bound
    {n : ℕ} (hn : 3 ≤ n) (S : Fin n × Fin n → ℤ)
    (hS_inj : Function.Injective S)
    (hS_range : ∀ c, 1 ≤ S c ∧ S c ≤ (n : ℤ) ^ 2)
    (j : Fin n) :
    let γ_j := (∑ i : Fin n, S (i, j)) - (n : ℤ) * ((n : ℤ) ^ 2 + 1) / 2
    |γ_j| ≤ (n : ℤ) ^ 2 * ((n : ℤ) - 1) / 2 := by
  have h := grid_arrangement_column_deviation_subset_sum_bound hn S hS_inj hS_range {j}
  simp only [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, one_mul] at h
  intro γ_j
  have heq : (n : ℤ) * ((n : ℤ) ^ 2 - (n : ℤ)) = (n : ℤ) ^ 2 * ((n : ℤ) - 1) := by ring
  rw [heq] at h
  exact h
