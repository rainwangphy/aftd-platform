import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointMaxProb
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointMaxValue

/-!
# spi_two_point_core

Topic: mechanism_design   Node: 0b931f7bd7c6

Real-arithmetic core of Proposition 3.1 for two-point rewards: accepted masses with posterior mean at least T have total at most spi_two_point_max_prob, and attaining it pins the accepted value to spi_two_point_max_value.
-/

/-- Real-arithmetic core of Prop. 3.1 for a two-point reward: accepted masses `a ≤ q` (on `h`) and `b ≤ 1 - q` (on `l`) with posterior mean at least `T` have total at most `spi_two_point_max_prob`, and attaining it pins the accepted value to `spi_two_point_max_value`. -/
lemma spi_two_point_core (h l q T a b : ℝ) (hlh : l ≤ h) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ q) (hb0 : 0 ≤ b) (hb1 : b ≤ 1 - q) (hc : T * (a + b) ≤ a * h + b * l) :
    a + b ≤ spi_two_point_max_prob h l q T ∧
      (spi_two_point_max_prob h l q T ≤ a + b → a * h + b * l = spi_two_point_max_value h l q T) := by
  unfold spi_two_point_max_prob spi_two_point_max_value
  split_ifs with h1 h2
  · refine ⟨by linarith, fun hP => ?_⟩
    have : a = q := by linarith
    have : b = 1 - q := by linarith
    subst_vars; ring
  · have hTl : l < T := by nlinarith
    have hTl' : 0 < T - l := by linarith
    have key : b * (T - l) ≤ a * (h - T) := by nlinarith
    refine ⟨?_, fun hP => ?_⟩
    · rw [le_div_iff₀ hTl']; nlinarith
    · rw [div_le_iff₀ hTl'] at hP
      have : a * (h - T) ≤ b * (T - l) := by nlinarith
      have hab : a + b = q * (h - l) / (T - l) := by
        rw [eq_div_iff hTl'.ne']; nlinarith
      rw [← hab]; nlinarith
  · have hab : (a + b) * (T - h) ≤ 0 := by nlinarith
    have : a + b ≤ 0 := by
      by_contra hneg; push Not at hneg
      have := mul_pos hneg (show 0 < T - h by linarith); linarith
    refine ⟨this, fun _ => ?_⟩
    have : a = 0 := by linarith
    have : b = 0 := by linarith
    subst_vars; ring
