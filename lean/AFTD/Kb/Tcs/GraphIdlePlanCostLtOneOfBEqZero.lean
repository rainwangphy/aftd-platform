import AFTD.Prelude

/-!
# graph_idle_plan_cost_lt_one_of_b_eq_zero

Topic: graphs   Node: e5126f9cda9e

Provenance: helper lemma. step towards exists_idle_measure_wasserstein_dist_lt_one_of_ediam_le_two_and_minDegree_ge

If b = 0 and 1 ≤ d_x, then 1/2 − (1/2)/d_x + 0 < 1.
-/

/-- Arithmetic: with b = 0 the main-plan cost bound is strictly below 1. -/
theorem graph_idle_plan_cost_lt_one_of_b_eq_zero
    (dx dy a b c : ℕ) (hdx : 1 ≤ dx) (hx : dx = a + c + 1) (hy : dy = b + c + 1) (hb : b = 0) :
    1/2 - (1/2)/(dx:ℝ) + 2*(b:ℝ)*((1/2)/(dy:ℝ)) < 1 := by
  subst hb
  have hdx' : (0:ℝ) < dx := by exact_mod_cast hdx
  have hnn : (0:ℝ) ≤ (1/2)/(dx:ℝ) := by positivity
  simp
  linarith
