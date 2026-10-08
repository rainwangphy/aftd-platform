import AFTD.Prelude

/-!
# integrable_exp_mul_sq_gaussianReal_zero

Topic: concentration   Node: 9bd3ee98da16

Provenance: helper lemma. TCSlib, `integrable_exp_mul_sq_gaussianReal_zero`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/ChiSquaredMGF.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Integrability of a Gaussian moment generating integrand. Let $v$ be a nonnegative real number with $v \ne 0$, and let $N(0,v)$ denote the centred
Gaussian probability measure on $\bbr$ with variance $v$. If $t \in \bbr$ satisfies $2tv
< 1$, then the function $y \mapsto e^{t y^2}$ is integrable with respect to $N(0,v)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- **Integrability of `exp(t · y²)` under `gaussianReal 0 v`.** For `v ≠ 0` and every real `t` with `2tv < 1`, the function `y ↦ exp(t y²)` is integrable with respect to the law `N(0, v)`. This is the integrability implicit in the finiteness of `E exp(sX²) = (1 − 2s)^{−1/2}` in [DG03, proof of Lemma 2.2]. **Proof sketch.** Step 1: write `N(0, v)` as Lebesgue measure with the Gaussian density, so integrability against it is integrability of the density times the integrand against Lebesgue measure. Step 2: rewrite the product pointwise as `(√(2πv))⁻¹ exp(−(1/(2v) − t) y²)`, where `b = 1/(2v) − t > 0` by the hypothesis. Step 3: `exp(−b y²)` is Lebesgue-integrable for `b > 0` (Mathlib's `integrable_exp_neg_mul_sq`); transfer along the pointwise identity. -/
lemma integrable_exp_mul_sq_gaussianReal_zero
    (v : ℝ≥0) (hv : v ≠ 0) (t : ℝ) (ht : 2 * t * (v : ℝ) < 1) :
    Integrable (fun y => Real.exp (t * y ^ 2)) (gaussianReal 0 v) := by
  -- Step 1: convert `gaussianReal 0 v` to `volume.withDensity (gaussianPDF 0 v)`.
  rw [gaussianReal_of_var_ne_zero _ hv]
  rw [integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
       (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  -- Goal: Integrable (fun y => (gaussianPDF 0 v y).toReal • exp(t y²)) volume.
  -- Rewrite the integrand as `(√(2πv))⁻¹ * exp(-(1/(2v) - t) y²)`, then use
  -- `integrable_exp_neg_mul_sq` with `b = 1/(2v) - t > 0`.
  have hv_pos : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have h2v_pos : 0 < 2 * (v : ℝ) := by linarith
  have hb_pos : 0 < 1 / (2 * (v : ℝ)) - t := by
    rw [sub_pos, lt_div_iff₀ h2v_pos]; linarith
  -- Step 2: pointwise rewrite of integrand.
  have h_eq : ∀ y : ℝ, (gaussianPDF 0 v y).toReal • Real.exp (t * y ^ 2) =
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
        Real.exp (-(1 / (2 * (v : ℝ)) - t) * y ^ 2) := by
    intro y
    rw [toReal_gaussianPDF, gaussianPDFReal, smul_eq_mul, sub_zero, mul_assoc,
        ← Real.exp_add]
    congr 2
    field_simp
    ring
  -- Step 3: integrability of the rewritten form.
  have h_int_rewritten : Integrable (fun y =>
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
        Real.exp (-(1 / (2 * (v : ℝ)) - t) * y ^ 2)) volume :=
    Integrable.const_mul (integrable_exp_neg_mul_sq hb_pos) _
  -- Transfer to original integrand via AE-equality.
  exact h_int_rewritten.congr (ae_of_all _ (fun y => (h_eq y).symm))
