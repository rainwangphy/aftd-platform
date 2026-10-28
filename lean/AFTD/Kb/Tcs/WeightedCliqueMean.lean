import AFTD.Prelude

/-!
# weighted_clique_mean

Topic: graphs   Node: e15bf1c39628

Provenance: helper lemma. step towards op_599_connected_induced_activity_clique_minimum

The lambda-weighted mean order of the complete graph K_n, equal to n * lam * (1+lam)^(n-1) / ((1+lam)^n - 1).
-/

/-- mu(n, lam) = n·lam·(1+lam)^(n-1)/((1+lam)^n − 1), the weighted mean order of K_n. -/
noncomputable def weighted_clique_mean (n : ℕ) (lam : ℝ) : ℝ := (n : ℝ) * lam * (1 + lam) ^ (n - 1) / ((1 + lam) ^ n - 1)
