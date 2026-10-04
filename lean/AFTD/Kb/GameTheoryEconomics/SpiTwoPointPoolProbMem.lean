import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointPoolProb

/-!
# spi_two_point_pool_prob_mem

Topic: mechanism_design   Node: e5eae95469c0

The pooling probability lies in [0, 1].
-/

/-- The pooling probability lies in `[0, 1]` for a two-point reward with `l ≤ h` and `q ∈ [0, 1]`. -/
lemma spi_two_point_pool_prob_mem (h l q T : ℝ) (hlh : l ≤ h) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ spi_two_point_pool_prob h l q T ∧ spi_two_point_pool_prob h l q T ≤ 1 := by
  unfold spi_two_point_pool_prob
  split_ifs with h1 h2
  · norm_num
  · have hq1' : q < 1 := by
      by_contra hc; push Not at hc
      have e : q * h + (1 - q) * l = h := by rw [le_antisymm hq1 hc]; ring
      linarith
    have hTl : 0 < T - l := by nlinarith
    have h1q : 0 < 1 - q := by linarith
    constructor
    · apply div_nonneg <;> nlinarith
    · rw [div_le_one (by positivity)]; nlinarith
  · norm_num
