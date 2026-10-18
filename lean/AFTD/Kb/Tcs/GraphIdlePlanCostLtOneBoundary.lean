import AFTD.Prelude

/-!
# graph_idle_plan_cost_lt_one_boundary

Topic: graphs   Node: a274b11386a2

Provenance: helper lemma. step towards exists_idle_measure_wasserstein_dist_lt_one_of_ediam_le_two_and_minDegree_ge

If d_x = a + c + 1 < d_y = b + c + 1 and b = c + 2, then 1/2 − (1/2)/d_x + 2b·(1/2)/d_y < 1.
-/

/-- Boundary arithmetic: with b = c+2 but d_x < d_y the main-plan cost bound is still below 1. -/
theorem graph_idle_plan_cost_lt_one_boundary
    (dx dy a b c : ℕ) (hdx : 1 ≤ dx) (hlt : dx < dy)
    (hx : dx = a + c + 1) (hy : dy = b + c + 1) (hb : b = c + 2) :
    1/2 - (1/2)/(dx:ℝ) + 2*(b:ℝ)*((1/2)/(dy:ℝ)) < 1 := by
  have hdxpos : (0:ℝ) < dx := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hdx)
  have hltR : (dx:ℝ) < (dy:ℝ) := by exact_mod_cast hlt
  have hdypos : (0:ℝ) < (dy:ℝ) := lt_trans hdxpos hltR
  have hbR : (b:ℝ) = (c:ℝ) + 2 := by exact_mod_cast hb
  have hyR : (dy:ℝ) = (b:ℝ) + (c:ℝ) + 1 := by exact_mod_cast hy
  have hdxR : (dx:ℝ) = (a:ℝ) + (c:ℝ) + 1 := by exact_mod_cast hx
  have key : 2*(b:ℝ)*((1/2)/(dy:ℝ)) = (1:ℝ)/2 + (1:ℝ)/(2*(dy:ℝ)) := by
    field_simp
    nlinarith
  rw [key]
  have h3 : (1:ℝ)/2/(dx:ℝ) = 1/(2*(dx:ℝ)) := by ring
  rw [h3]
  have h2 : (1:ℝ)/(2*(dy:ℝ)) < 1/(2*(dx:ℝ)) := by
    apply one_div_lt_one_div_of_lt
    · positivity
    · linarith
  linarith
