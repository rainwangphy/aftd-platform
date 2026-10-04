import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiSearcherPayoff
import AFTD.Kb.GameTheoryEconomics.SpiIsEquilibrium
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointMaxProb
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointMaxValue
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointEquilibriumPinned
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointAbove
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointMaxMid
import AFTD.Kb.GameTheoryEconomics.SpiReachProbFinFour
import AFTD.Kb.GameTheoryEconomics.SpxX
import AFTD.Kb.GameTheoryEconomics.SpxW
import AFTD.Kb.GameTheoryEconomics.SpxInstance
import AFTD.Kb.GameTheoryEconomics.SpxVals

/-!
# spx_payoff_mid

Topic: mechanism_design   Node: 4107e830d304

For 24/5 < T <= 9, every equilibrium of the four-player instance gives the searcher T p1 + (1-p1)(10/3 + (1-p2) 8/5) with p1 = (3/5)/(T-3), p2 = (10/3)/T.
-/

open Finset in
/-- In any equilibrium with threshold `24/5 < T ≤ 9`, the searcher's payoff in the four-player instance is `T p₁ + (1 - p₁)(10/3 + (1 - p₂) 8/5)` with `p₁ = (3/5)/(T - 3)` and `p₂ = (10/3)/T`. -/
lemma spx_payoff_mid {S : ℕ} (hS : 2 ≤ S) (T : ℝ) (φ : Fin 4 → Fin 2 → Fin S → ℝ)
    (heq : spi_is_equilibrium spx_x spx_w T φ) (hT1 : 24 / 5 < T) (hT2 : T ≤ 9) :
    spi_searcher_payoff spx_x spx_w φ T =
      T * ((3 / 5) / (T - 3)) + (1 - (3 / 5) / (T - 3)) * (10 / 3 + (1 - (10 / 3) / T) * (8 / 5)) := by
  obtain ⟨r0, r1, r2, r3⟩ := spi_reach_prob_fin_four spx_x spx_w φ T
  have a0 := spi_two_point_above spx_x spx_w spx_instance T φ (i := 0) (heq.1 0)
    (by simp [spx_x]; linarith)
  have p1 := spi_two_point_equilibrium_pinned hS spx_x spx_w spx_instance T φ heq 1
    (by rw [r1, a0.1]; norm_num)
  have hT3 : 0 < T - 3 := by linarith
  obtain ⟨x00, x01, w00, x10, x11, w10, x20, x21, w20, x30, x31, w30⟩ := spx_vals
  have mid1 := spi_two_point_max_mid 9 3 (1 / 10) T (by norm_num; linarith) hT2
  have hm1 : spi_two_point_max_prob (spx_x 1 0) (spx_x 1 1) (spx_w 1 0) T = (3 / 5) / (T - 3) := by
    rw [x10, x11, w10, mid1.1]; ring
  have hv1 : spi_two_point_max_value (spx_x 1 0) (spx_x 1 1) (spx_w 1 0) T = T * ((3 / 5) / (T - 3)) := by
    rw [x10, x11, w10, mid1.2]; ring
  have hP1 : (3 / 5) / (T - 3) < 1 := by rw [div_lt_one hT3]; linarith
  have p2 := spi_two_point_equilibrium_pinned hS spx_x spx_w spx_instance T φ heq 2
    (by rw [r2, a0.1, p1.1, hm1]; nlinarith)
  have mid2 := spi_two_point_max_mid 1000 0 (1 / 300) T (by norm_num; linarith) (by linarith)
  have hm2 : spi_two_point_max_prob (spx_x 2 0) (spx_x 2 1) (spx_w 2 0) T = (10 / 3) / T := by
    rw [x20, x21, w20, mid2.1]; ring
  have hv2 : spi_two_point_max_value (spx_x 2 0) (spx_x 2 1) (spx_w 2 0) T = 10 / 3 := by
    rw [x20, x21, w20, mid2.2]; have hT0' : T ≠ 0 := by linarith
    field_simp; try ring
  have hP2 : (10 / 3) / T < 1 := by rw [div_lt_one (by linarith)]; linarith
  have p3 := spi_two_point_equilibrium_pinned hS spx_x spx_w spx_instance T φ heq 3
    (by rw [r3, a0.1, p1.1, p2.1, hm1, hm2]; apply mul_pos <;> nlinarith)
  have mid3 := spi_two_point_max_mid 40 0 (1 / 25) T (by norm_num; linarith) (by linarith)
  have hv3 : spi_two_point_max_value (spx_x 3 0) (spx_x 3 1) (spx_w 3 0) T = 8 / 5 := by
    rw [x30, x31, w30, mid3.2]; have hT0' : T ≠ 0 := by linarith
    field_simp; try ring
  simp only [spi_searcher_payoff, Fin.sum_univ_four, r0, r1, r2, r3, a0.1, a0.2, p1.1, p1.2, p2.1, p2.2,
    p3.2, hm1, hv1, hm2, hv2, hv3]
  ring
