import AFTD.Prelude
import AFTD.Kb.Tcs.GraphEdgePartitionCard

/-!
# graph_idle_special_cost_lt_one

Topic: graphs   Node: 3a0d2700c128

Provenance: helper lemma. step towards exists_idle_measure_wasserstein_dist_lt_one_of_ediam_le_two_and_minDegree_ge

If a = b, b = c + 2 and d_y = b + c + 1, then 1/2 + 2(a−1)·(1/2)/d_y < 1.
-/

/-- Arithmetic: in the boundary configuration 1/2 + 2(|A|-1)(1/2)/d_y < 1. -/
theorem graph_idle_special_cost_lt_one
    (a b c dy : ℕ) (ha : a = b) (hb : b = c + 2) (hdy : dy = b + c + 1) :
    (1:ℝ)/2 + 2*((a:ℝ) - 1)*((1/2)/(dy:ℝ)) < 1 := by
  have hdypos : (0:ℝ) < dy := by
    have : 0 < dy := by omega
    exact_mod_cast this
  have hdy' : (dy:ℝ) = 2*(c:ℝ) + 3 := by
    have : (dy:ℝ) = (b:ℝ) + (c:ℝ) + 1 := by exact_mod_cast hdy
    have : (b:ℝ) = (c:ℝ) + 2 := by exact_mod_cast hb
    nlinarith
  have ha' : (a:ℝ) = (c:ℝ) + 2 := by
    have : (a:ℝ) = (b:ℝ) := by exact_mod_cast ha
    have : (b:ℝ) = (c:ℝ) + 2 := by exact_mod_cast hb
    nlinarith
  rw [hdy', ha']
  have hden : (2*(c:ℝ) + 3) ≠ (0:ℝ) := by positivity
  field_simp [hden]
  ring_nf
  have hc : (0:ℝ) ≤ (c:ℝ) := Nat.cast_nonneg c
  nlinarith [hc]
