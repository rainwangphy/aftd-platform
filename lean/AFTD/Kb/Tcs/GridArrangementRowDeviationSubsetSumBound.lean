import AFTD.Prelude
import AFTD.Kb.Tcs.GridArrangementColumnDeviationSubsetSumBound

/-!
# grid_arrangement_row_deviation_subset_sum_bound

Topic: combinatorics   Node: 21f9f4b64bbd

Provenance: formalization of a published result. Source: arXiv:2610.38386 Lemma 3.8

Let $n \ge 3$, $N = n^2$, and let $S : \mathrm{Fin}\ n \times \mathrm{Fin}\ n \to \mathbb{Z}$ be an injective arrangement with entries in $\{1, \dots, N\}$. For the row-deviation vector $\rho_i = \sum_{j=0}^{n-1} S(i,j) - n(N+1)/2$ and any subset of rows $I \subseteq \mathrm{Fin}\ n$ of cardinality $p = |I|$, $|\sum_{i \in I} \rho_i| \le pn(N-pn)/2$.
-/

/-- Majorisation bound for row-deviation subset sums of a grid arrangement. -/
theorem grid_arrangement_row_deviation_subset_sum_bound
    {n : ℕ} (hn : 3 ≤ n) (S : Fin n × Fin n → ℤ)
    (hS_inj : Function.Injective S)
    (hS_range : ∀ c, 1 ≤ S c ∧ S c ≤ (n : ℤ) ^ 2)
    (I : Finset (Fin n)) :
    let ρ := fun i => (∑ j : Fin n, S (i, j)) - (n : ℤ) * ((n : ℤ) ^ 2 + 1) / 2
    let p := I.card
    let N := (n : ℤ) ^ 2
    |∑ i ∈ I, ρ i| ≤ (p : ℤ) * (n : ℤ) * (N - (p : ℤ) * (n : ℤ)) / 2 := by
  intro ρ p N
  let S_trans : Fin n × Fin n → ℤ := fun c => S (c.2, c.1)
  have hS_trans_inj : Function.Injective S_trans := by
    intro ⟨a1, b1⟩ ⟨a2, b2⟩ h
    dsimp [S_trans] at h
    have := hS_inj h
    cases this
    rfl
  have hS_trans_range : ∀ c, 1 ≤ S_trans c ∧ S_trans c ≤ (n : ℤ) ^ 2 := by
    intro c
    exact hS_range (c.2, c.1)
  have h_bound := grid_arrangement_column_deviation_subset_sum_bound hn S_trans hS_trans_inj hS_trans_range I
  dsimp at h_bound
  exact h_bound
