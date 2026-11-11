import AFTD.Prelude
import AFTD.Kb.Tcs.FourierCrossLevel
import AFTD.Kb.Tcs.FourierVariance
import AFTD.Kb.Tcs.FourierCrossLevelEqZeroOfCardLt
import AFTD.Kb.Tcs.FourierCrossLevelOneLeSqrtVarianceMul
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# discrete_level_one_to_three_sharp_constant_of_lt_three

Topic: combinatorics   Node: 335acc907eab

Provenance: helper lemma. step towards discrete_level_one_to_three_sharp_constant

The sharp level 1 to 3 inequality holds for all n < 3 (i.e. n = 1, 2) because W_3[f,g] = 0 and the left-hand side is nonpositive by Cauchy-Schwarz.
-/

/-- Sharp level 1 to 3 inequality for dimensions n < 3 (arXiv:2611.08289 Question 6.1). -/
theorem discrete_level_one_to_three_sharp_constant_of_lt_three (n : ℕ) (hn : 1 ≤ n) (hn3 : n < 3)
    (f g : BooleanAnalysis.BooleanFunc n) (hf : Monotone f) (hg : Monotone g)
    (hw : 0 < fourier_cross_level 1 f g) :
    - (fourier_cross_level 1 f g / (3 * Real.log (4 / 3))) *
        Real.log (Real.sqrt (fourier_variance f * fourier_variance g) / fourier_cross_level 1 f g) ≤
      fourier_cross_level 3 f g := by
  have hW3 : fourier_cross_level 3 f g = 0 :=
    fourier_cross_level_eq_zero_of_card_lt hn3 f g
  rw [hW3]
  have hA : 0 < fourier_cross_level 1 f g := hw
  have hCS := fourier_cross_level_one_le_sqrt_variance_mul f g
  have hratio :
      1 ≤ Real.sqrt (fourier_variance f * fourier_variance g) / fourier_cross_level 1 f g := by
    rw [le_div_iff₀ hA]
    simpa using hCS
  have hlog :
      0 ≤ Real.log (Real.sqrt (fourier_variance f * fourier_variance g) /
        fourier_cross_level 1 f g) :=
    Real.log_nonneg hratio
  have hden : 0 < 3 * Real.log (4 / 3 : ℝ) := by
    have h : (1 : ℝ) < 4 / 3 := by norm_num
    have := Real.log_pos h
    positivity
  have hcoef : 0 < fourier_cross_level 1 f g / (3 * Real.log (4 / 3 : ℝ)) :=
    div_pos hA hden
  have hprod : 0 ≤
      fourier_cross_level 1 f g / (3 * Real.log (4 / 3 : ℝ)) *
        Real.log (Real.sqrt (fourier_variance f * fourier_variance g) /
          fourier_cross_level 1 f g) :=
    mul_nonneg (le_of_lt hcoef) hlog
  simpa [neg_mul] using neg_nonpos.mpr hprod
