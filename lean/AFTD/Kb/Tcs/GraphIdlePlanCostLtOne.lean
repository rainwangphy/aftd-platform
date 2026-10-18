import AFTD.Prelude

/-!
# graph_idle_plan_cost_lt_one

Topic: graphs   Node: c6dcf22197b4

Provenance: helper lemma. step towards exists_idle_measure_wasserstein_dist_lt_one_of_ediam_le_two_and_minDegree_ge

If d_x = a + c + 1, d_y = b + c + 1, 1 ≤ d_x ≤ d_y and b ≤ c + 1, then 1/2 − (1/2)/d_x + 2b·(1/2)/d_y < 1.
-/

/-- Arithmetic: with b ≤ c+1 the main-plan cost bound is strictly below 1. -/
theorem graph_idle_plan_cost_lt_one
    (dx dy a b c : ℕ) (hdx : 1 ≤ dx) (hle : dx ≤ dy)
    (hx : dx = a + c + 1) (hy : dy = b + c + 1) (hb : b ≤ c + 1) :
    1/2 - (1/2)/(dx:ℝ) + 2*(b:ℝ)*((1/2)/(dy:ℝ)) < 1 := by
  have hdx' : (1:ℝ) ≤ (dx:ℝ) := by exact_mod_cast hdx
  have hle' : (dx:ℝ) ≤ (dy:ℝ) := by exact_mod_cast hle
  have hx' : (dx:ℝ) = (a:ℝ) + (c:ℝ) + 1 := by exact_mod_cast hx
  have hy' : (dy:ℝ) = (b:ℝ) + (c:ℝ) + 1 := by exact_mod_cast hy
  have hb' : (b:ℝ) ≤ (c:ℝ) + 1 := by exact_mod_cast hb
  have hdy : (0:ℝ) < (dy:ℝ) := by linarith
  have hdxpos : (0:ℝ) < (dx:ℝ) := by linarith
  have hdypos : (0:ℝ) < (dy:ℝ) := by linarith
  rw [hx', hy']
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hb' (by positivity : (0:ℝ) ≤ (b:ℝ))]
