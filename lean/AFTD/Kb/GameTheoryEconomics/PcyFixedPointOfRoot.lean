import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PcpVenueImpact
import AFTD.Kb.GameTheoryEconomics.PcpHalfTwoAction
import AFTD.Kb.GameTheoryEconomics.PcyTheta
import AFTD.Kb.GameTheoryEconomics.PcyMu
import AFTD.Kb.GameTheoryEconomics.PcyCost
import AFTD.Kb.GameTheoryEconomics.PcyImpact
import AFTD.Kb.GameTheoryEconomics.PcyPoly

/-!
# pcy_fixed_point_of_root

Topic: equilibria   Node: 259729e3701d

For y > 0 the venue-0 impact of the three-type instance is positive, and a root of pcy_poly gives the fixed-point condition u_1 = y u_0.
-/

open Finset in
/-- For `y > 0`, the impact of venue 0 is positive, and a root of `pcy_poly` gives the fixed-point condition `pcy_impact y 1 = y * pcy_impact y 0`. -/
lemma pcy_fixed_point_of_root (y : ℝ) (hy : 0 < y) :
    0 < pcy_impact y 0 ∧ (pcy_poly y = 0 → pcy_impact y 1 = y * pcy_impact y 0) := by
  have h1 : (0 : ℝ) < 128 + y ^ 4 := by positivity
  have h2 : (0 : ℝ) < 64 + y ^ 4 := by positivity
  have h3 : (0 : ℝ) < 8 + y ^ 4 := by positivity
  have hy4 : (0 : ℝ) < y ^ 4 := by positivity
  simp only [pcy_impact, pcp_venue_impact, pcp_half_two_action, Fin.sum_univ_three, Fin.sum_univ_two,
    pcy_cost, pcy_mu, pcy_theta]
  simp
  constructor
  · positivity
  · intro hP
    have hE : (0 : ℝ) < (3 / 10 / 128) * ((64 + y ^ 4) * (8 + y ^ 4)) + (1 / 20 / 64) * ((128 + y ^ 4) * (8 + y ^ 4)) +
      (13 / 20 / 8) * ((128 + y ^ 4) * (64 + y ^ 4)) := by positivity
    have hB : (0 : ℝ) < (3 / 10 * 128) * ((64 + y ^ 4) * (8 + y ^ 4)) + (1 / 20 * 64) * ((128 + y ^ 4) * (8 + y ^ 4)) +
      (13 / 20 * 8) * ((128 + y ^ 4) * (64 + y ^ 4)) := by positivity
    rw [← sub_eq_zero]
    rw [show pcy_poly y = 0 ↔ pcy_poly y / (((3 / 10 / 128) * ((64 + y ^ 4) * (8 + y ^ 4)) +
        (1 / 20 / 64) * ((128 + y ^ 4) * (8 + y ^ 4)) + (13 / 20 / 8) * ((128 + y ^ 4) * (64 + y ^ 4))) *
        ((3 / 10 * 128) * ((64 + y ^ 4) * (8 + y ^ 4)) + (1 / 20 * 64) * ((128 + y ^ 4) * (8 + y ^ 4)) +
        (13 / 20 * 8) * ((128 + y ^ 4) * (64 + y ^ 4)))) = 0 by
          rw [div_eq_zero_iff]; constructor
          · exact Or.inl
          · rintro (h | h)
            · exact h
            · exact absurd h (mul_pos hE hB).ne'] at hP
    rw [← hP, pcy_poly]
    field_simp
