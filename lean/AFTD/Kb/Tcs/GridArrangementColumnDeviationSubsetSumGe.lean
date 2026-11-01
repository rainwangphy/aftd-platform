import AFTD.Prelude
import AFTD.Kb.Tcs.GridArrangementColumnDeviationSubsetSumBound

/-!
# grid_arrangement_column_deviation_subset_sum_ge

Topic: combinatorics   Node: d4321df8d297

Provenance: helper lemma. arXiv:2610.38386 Lemma 3.8

For any grid arrangement $S$ of order $n \ge 3$ and any column subset $J$ of cardinality $p$, the column-deviation sum $\sum_{j \in J} \gamma_j$ is bounded below by $-pn(N-pn)/2$.
-/

/-- Lower bound for column-deviation subset sum by the sum of the smallest entries. -/
theorem grid_arrangement_column_deviation_subset_sum_ge
    {n : ℕ} (hn : 3 ≤ n) (S : Fin n × Fin n → ℤ)
    (hS_inj : Function.Injective S)
    (hS_range : ∀ c, 1 ≤ S c ∧ S c ≤ (n : ℤ) ^ 2)
    (J : Finset (Fin n)) :
    let γ := fun j => (∑ i : Fin n, S (i, j)) - (n : ℤ) * ((n : ℤ) ^ 2 + 1) / 2
    let p := J.card
    let N := (n : ℤ) ^ 2
    (-((p : ℤ) * (n : ℤ) * (N - (p : ℤ) * (n : ℤ)) / 2)) ≤ ∑ j ∈ J, γ j := by
  intro γ p N
  have h := grid_arrangement_column_deviation_subset_sum_bound hn S hS_inj hS_range J
  exact (abs_le.mp h).1
