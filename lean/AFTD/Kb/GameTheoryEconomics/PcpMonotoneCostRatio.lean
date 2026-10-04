import AFTD.Prelude

/-!
# pcp_monotone_cost_ratio

Topic: equilibria   Node: 729bca194c5d

Assumption 1 (Monotone Cost Ratio): for types theta_i < theta_i' and venues j < j', c_ij / c_i'j < c_ij' / c_i'j'.
-/

/-- Assumption 1 (Monotone Cost Ratio) of arXiv:2511.13678: for types `θ i < θ i'` and venues `j < j'`, `c i j / c i' j < c i j' / c i' j'`. -/
def pcp_monotone_cost_ratio {n k : ℕ} (θ : Fin n → ℝ) (c : Fin n → Fin k → ℝ) : Prop :=
  ∀ (i i' : Fin n) (j j' : Fin k), θ i < θ i' → j < j' → c i j / c i' j < c i j' / c i' j'
