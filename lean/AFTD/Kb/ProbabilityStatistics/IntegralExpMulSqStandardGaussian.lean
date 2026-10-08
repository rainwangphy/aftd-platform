import AFTD.Prelude

/-!
# integral_exp_mul_sq_standardGaussian

Topic: concentration   Node: 6eed0f66be6a

Provenance: helper lemma. TCSlib, `integral_exp_mul_sq_standardGaussian`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/ChiSquaredMGF.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Quadratic Gaussian integral. Let $Z$ be a standard Gaussian random variable, $Z \sim N(0,1)$, and let $s \in \bbr$
satisfy $2s < 1$. Then
\[
  \E\!\left[e^{s Z^2}\right]
  = \int_{\bbr} e^{s z^2}\, \mathrm{d}N(0,1)(z)
  = \frac{1}{\sqrt{1 - 2s}}.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- **Standard Gaussian quadratic MGF closed form.** For `Z ~ N(0, 1)` and every real `s` with `2s < 1`, the integral of `exp(s z²)` against the standard Gaussian law equals `1/√(1 − 2s)`. This is the moment generating function of a chi-squared variable with one degree of freedom, `E exp(sX²) = (1 − 2s)^{−1/2}`, used in [DG03, proof of Lemma 2.2]. **Proof sketch.** Step 1: rewrite the integral against the Gaussian density `(√(2π))⁻¹ exp(−z²/2)` and merge the two exponentials into `(√(2π))⁻¹ exp(−(1/2 − s) z²)`. Step 2: pull out the constant and evaluate the Gaussian integral `∫ exp(−b z²) = √(π/b)` with `b = 1/2 − s > 0` (Mathlib's `integral_gaussian`). Step 3: simplify `(√(2π))⁻¹ √(π/(1/2 − s))` to `1/√(1 − 2s)` by clearing the square roots. -/
lemma integral_exp_mul_sq_standardGaussian
    (s : ℝ) (hs : 2 * s < 1) :
    ∫ z, Real.exp (s * z ^ 2) ∂(gaussianReal 0 1) =
      1 / Real.sqrt (1 - 2 * s) := by
  have hv1 : ((1 : ℝ≥0) : ℝ) ≠ 0 := by simp
  have hb_pos : 0 < (1 : ℝ) / 2 - s := by linarith
  -- Step 1: rewrite the integrand against the PDF.
  rw [integral_gaussianReal_eq_integral_smul (by simp : (1 : ℝ≥0) ≠ 0)]
  -- Combine the two exponentials: PDF is `(√(2π))⁻¹ exp(-z²/2)`, multiplying by `exp(s z²)`
  -- gives `(√(2π))⁻¹ exp(-(1/2 - s) z²)`.
  have h_int_eq : ∀ z : ℝ,
      gaussianPDFReal 0 1 z • Real.exp (s * z ^ 2)
        = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1/2 - s) * z ^ 2) := by
    intro z
    simp only [gaussianPDFReal, smul_eq_mul, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [h_int_eq]
  -- Step 2: pull out the constant and evaluate the Gaussian integral.
  rw [integral_const_mul, integral_gaussian (1/2 - s)]
  -- Step 3: now show `(√(2π))⁻¹ * √(π / (1/2 - s)) = 1 / √(1 - 2s)`.
  -- Multiply both sides by √(2π) * √(1 - 2s) and check using sq_eq_sq.
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hb_pos' : (0 : ℝ) < 1 - 2 * s := by linarith
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hdiv_pos : (0 : ℝ) < Real.pi / (1/2 - s) := div_pos hpi_pos hb_pos
  have h_sq2pi : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr h2pi_pos).ne'
  have h_sq1m2s : Real.sqrt (1 - 2 * s) ≠ 0 := (Real.sqrt_pos.mpr hb_pos').ne'
  rw [eq_div_iff h_sq1m2s]
  rw [show (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / (1/2 - s)) * Real.sqrt (1 - 2*s)
        = (Real.sqrt (Real.pi / (1/2 - s)) * Real.sqrt (1 - 2*s)) / Real.sqrt (2 * Real.pi) by
      ring]
  rw [div_eq_one_iff_eq h_sq2pi]
  rw [← Real.sqrt_mul hdiv_pos.le]
  congr 1
  field_simp
