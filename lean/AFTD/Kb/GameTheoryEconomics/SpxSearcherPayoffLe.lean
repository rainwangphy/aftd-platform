import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiSearcherPayoff
import AFTD.Kb.GameTheoryEconomics.SpiIsEquilibrium
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointMaxProb
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointMaxValue
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointEquilibriumPinned
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointAbove
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointMaxLow
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointMaxMid
import AFTD.Kb.GameTheoryEconomics.SpiReachProbFinFour
import AFTD.Kb.GameTheoryEconomics.SpxX
import AFTD.Kb.GameTheoryEconomics.SpxW
import AFTD.Kb.GameTheoryEconomics.SpxInstance
import AFTD.Kb.GameTheoryEconomics.SpxVals
import AFTD.Kb.GameTheoryEconomics.SpxPayoffMid

/-!
# spx_searcher_payoff_le

Topic: mechanism_design   Node: 55ca848658c6

In the four-player instance, for every static threshold T, every S >= 2 and every equilibrium, the searcher's expected payoff is at most 721/150.
-/

open Finset in
/-- In the four-player instance, for every static threshold `T`, every number `S ≥ 2` of signals and every equilibrium of the players' signaling game, the searcher's expected payoff is at most `721/150`. -/
theorem spx_searcher_payoff_le {S : ℕ} (hS : 2 ≤ S) (T : ℝ) (φ : Fin 4 → Fin 2 → Fin S → ℝ)
    (heq : spi_is_equilibrium spx_x spx_w T φ) :
    spi_searcher_payoff spx_x spx_w φ T ≤ 721 / 150 := by
  obtain ⟨r0, r1, r2, r3⟩ := spi_reach_prob_fin_four spx_x spx_w φ T
  have p0 := spi_two_point_equilibrium_pinned hS spx_x spx_w spx_instance T φ heq 0 (by rw [r0]; norm_num)
  obtain ⟨x00, x01, w00, x10, x11, w10, x20, x21, w20, x30, x31, w30⟩ := spx_vals
  by_cases hA : T ≤ 24 / 5
  · have low0 := spi_two_point_max_low (24 / 5) 0 1 T (by norm_num; linarith)
    have hm0 : spi_two_point_max_prob (spx_x 0 0) (spx_x 0 1) (spx_w 0 0) T = 1 := by
      rw [x00, x01, w00, low0.1]
    have hv0 : spi_two_point_max_value (spx_x 0 0) (spx_x 0 1) (spx_w 0 0) T = 24 / 5 := by
      rw [x00, x01, w00, low0.2]; norm_num
    simp only [spi_searcher_payoff, Fin.sum_univ_four, r0, r1, r2, r3, p0.1, p0.2, hm0, hv0]
    norm_num
  push Not at hA
  by_cases hB : T ≤ 9
  · rw [spx_payoff_mid hS T φ heq hA hB]
    have hT3 : 0 < T - 3 := by linarith
    have hT0 : 0 < T := by linarith
    have key : T * ((3 / 5) / (T - 3)) + (1 - (3 / 5) / (T - 3)) * (10 / 3 + (1 - (10 / 3) / T) * (8 / 5)) =
        721 / 150 - (9 - T) * (109 * T - 320) / (150 * T * (T - 3)) := by
      field_simp; ring
    have hnn : 0 ≤ (9 - T) * (109 * T - 320) / (150 * T * (T - 3)) := by
      apply div_nonneg
      · apply mul_nonneg <;> linarith
      · positivity
    linarith
  push Not at hB
  have a0 := spi_two_point_above spx_x spx_w spx_instance T φ (i := 0) (heq.1 0) (by simp [spx_x]; linarith)
  have a1 := spi_two_point_above spx_x spx_w spx_instance T φ (i := 1) (heq.1 1) (by simp [spx_x]; linarith)
  by_cases hC : T ≤ 1000
  · have p2 := spi_two_point_equilibrium_pinned hS spx_x spx_w spx_instance T φ heq 2
      (by rw [r2, a0.1, a1.1]; norm_num)
    have mid2 := spi_two_point_max_mid 1000 0 (1 / 300) T (by norm_num; linarith) hC
    have hm2 : spi_two_point_max_prob (spx_x 2 0) (spx_x 2 1) (spx_w 2 0) T = (10 / 3) / T := by
      rw [x20, x21, w20, mid2.1]; ring
    have hv2 : spi_two_point_max_value (spx_x 2 0) (spx_x 2 1) (spx_w 2 0) T = 10 / 3 := by
      have hT0' : T ≠ 0 := by linarith
      rw [x20, x21, w20, mid2.2]; field_simp; try ring
    have hT0 : 0 < T := by linarith
    by_cases hD : T ≤ 40
    · have p3 := spi_two_point_equilibrium_pinned hS spx_x spx_w spx_instance T φ heq 3
        (by
          rw [r3, a0.1, a1.1, p2.1, hm2]
          have hP2 : (10 / 3) / T < 1 := by rw [div_lt_one hT0]; linarith
          simp only [sub_zero, one_mul]; linarith)
      have mid3 := spi_two_point_max_mid 40 0 (1 / 25) T (by norm_num; linarith) hD
      have hv3 : spi_two_point_max_value (spx_x 3 0) (spx_x 3 1) (spx_w 3 0) T = 8 / 5 := by
        have hT0' : T ≠ 0 := by linarith
        rw [x30, x31, w30, mid3.2]; field_simp; try ring
      simp only [spi_searcher_payoff, Fin.sum_univ_four, r0, r1, r2, r3, a0.1, a0.2, a1.1, a1.2, p2.1, p2.2,
        p3.2, hm2, hv2, hv3]
      have : (10 / 3) / T ≥ 1 / 12 := by rw [ge_iff_le, le_div_iff₀ hT0]; linarith
      nlinarith
    · push Not at hD
      have a3 := spi_two_point_above spx_x spx_w spx_instance T φ (i := 3) (heq.1 3) (by simp [spx_x]; linarith)
      simp only [spi_searcher_payoff, Fin.sum_univ_four, r0, r1, r2, r3, a0.1, a0.2, a1.1, a1.2, p2.1, p2.2,
        a3.2, hv2]
      norm_num
  · push Not at hC
    have a2 := spi_two_point_above spx_x spx_w spx_instance T φ (i := 2) (heq.1 2) (by simp [spx_x]; linarith)
    have a3 := spi_two_point_above spx_x spx_w spx_instance T φ (i := 3) (heq.1 3) (by simp [spx_x]; linarith)
    simp only [spi_searcher_payoff, Fin.sum_univ_four, r0, r1, r2, r3, a0.2, a1.2, a2.2, a3.2]
    norm_num
