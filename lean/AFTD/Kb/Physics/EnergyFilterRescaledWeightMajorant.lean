import AFTD.Prelude

/-!
# energy_filter_rescaled_weight_majorant

Topic: statistical_mechanics   Node: f0aec2f98d64

Provenance: helper lemma. OP-892: direct shifted-binomial kernel limit and uniform bound.

If b≤exp(−y²/2) and |x−y|≤1, then b≤exp(1/2)exp(−x²/4).
-/

theorem energy_filter_rescaled_weight_majorant (b x y : ℝ)
    (hb : b ≤ Real.exp (-(y^2/2))) (hxy : |x-y| ≤ 1) :
    b ≤ Real.exp (1/2) * Real.exp (-(x^2/4)) := by
  have hdist := abs_le.mp hxy
  have hsq : (x-y)^2 ≤ 1 := by nlinarith
  have hquad : -(y^2/2) ≤ 1/2-x^2/4 := by nlinarith [sq_nonneg (x-2*y)]
  calc
    b ≤ Real.exp (-(y^2/2)) := hb
    _ ≤ Real.exp (1/2-x^2/4) := Real.exp_le_exp.mpr hquad
    _ = Real.exp (1/2) * Real.exp (-(x^2/4)) := by rw [← Real.exp_add]; congr 1
