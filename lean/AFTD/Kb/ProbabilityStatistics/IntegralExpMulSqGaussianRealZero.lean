import AFTD.Prelude
import AFTD.Kb.ProbabilityStatistics.IntegralExpMulSqStandardGaussian

/-!
# integral_exp_mul_sq_gaussianReal_zero

Topic: concentration   Node: 0f6998162d71

Provenance: helper lemma. TCSlib, `integral_exp_mul_sq_gaussianReal_zero`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/ChiSquaredMGF.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Quadratic exponential integral against a centered Gaussian. Let $v > 0$ and write $N(0,v)$ for the centered Gaussian distribution on $\bbr$ with
mean $0$ and variance $v$. Then for every real number $t$ with $2tv < 1$,
\[
  \int_{\bbr} e^{t y^2}\, \mathrm{d}N(0,v)(y) = \frac{1}{\sqrt{1 - 2tv}}.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- **Gaussian quadratic MGF closed form** for general variance. For `Y ~ N(0, v)` with `v ≠ 0` and every real `t` with `2tv < 1`, the integral of `exp(t y²)` against the law `N(0, v)` equals `1/√(1 − 2tv)`. This is the scaled form of `E exp(sX²) = (1 − 2s)^{−1/2}` in [DG03, proof of Lemma 2.2]. **Proof sketch.** Step 1: `N(0, v)` is the pushforward of `N(0, 1)` under multiplication by `√v` (Mathlib's `gaussianReal_map_const_mul`). Step 2: change variables in the integral, so the integrand becomes `exp((tv) z²)` against `N(0, 1)`. Step 3: apply the standard-Gaussian closed form `integral_exp_mul_sq_standardGaussian` with `s = tv` (admissible since `2tv < 1`) and match the expression. -/
lemma integral_exp_mul_sq_gaussianReal_zero
    (v : ℝ≥0) (hv : v ≠ 0) (t : ℝ) (ht : 2 * t * (v : ℝ) < 1) :
    ∫ y, Real.exp (t * y ^ 2) ∂(gaussianReal 0 v) =
      1 / Real.sqrt (1 - 2 * t * (v : ℝ)) := by
  -- Step 1: push forward N(0,1) by multiplication by √v to get N(0,v).
  have hv_pos : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hv_nonneg : (0 : ℝ) ≤ (v : ℝ) := hv_pos.le
  have h_sqrt_sq : Real.sqrt (v : ℝ) ^ 2 = (v : ℝ) := Real.sq_sqrt hv_nonneg
  -- Identity: (gaussianReal 0 1).map (√v * ·) = gaussianReal 0 v.
  have h_map : (gaussianReal 0 1).map (fun z => Real.sqrt (v : ℝ) * z)
      = gaussianReal 0 v := by
    have := gaussianReal_map_const_mul (μ := 0) (v := (1 : ℝ≥0)) (Real.sqrt (v : ℝ))
    simp only [mul_zero] at this
    rw [this]
    congr 1
    rw [mul_one]
    apply NNReal.coe_injective
    simp [h_sqrt_sq]
  -- Step 2: reduce the integral to one against gaussianReal 0 1.
  rw [← h_map]
  rw [integral_map]
  · -- Now integral is ∫ z, exp(t * (√v * z)²) ∂(gaussianReal 0 1).
    have h_eq : ∀ z : ℝ, Real.exp (t * (Real.sqrt (v : ℝ) * z) ^ 2)
        = Real.exp ((t * (v : ℝ)) * z ^ 2) := by
      intro z
      congr 1
      rw [mul_pow, h_sqrt_sq]
      ring
    simp_rw [h_eq]
    -- Step 3: apply variance-1 lemma with s = t * v.
    have hs : 2 * (t * (v : ℝ)) < 1 := by
      have : 2 * t * (v : ℝ) = 2 * (t * (v : ℝ)) := by ring
      linarith [ht, this]
    rw [integral_exp_mul_sq_standardGaussian (t * (v : ℝ)) hs]
    congr 2
    ring
  · exact (measurable_const.mul measurable_id).aemeasurable
  · -- AEStronglyMeasurable of fun y => exp (t * y^2) under the pushforward
    apply Measurable.aestronglyMeasurable
    exact (measurable_const.mul (measurable_id.pow_const _)).exp
