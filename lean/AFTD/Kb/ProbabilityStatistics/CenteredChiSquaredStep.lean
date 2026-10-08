import AFTD.Prelude
import AFTD.Kb.ProbabilityStatistics.IntegrableExpMulSqGaussianRealZero
import AFTD.Kb.ProbabilityStatistics.IntegralExpMulSqGaussianRealZero
import AFTD.Kb.ProbabilityStatistics.NegLogOneSubTwoMulLeTwoSq

/-!
# centered_chi_squared_step

Topic: concentration   Node: 1ab5b6a0c616

Provenance: helper lemma. TCSlib, `centered_chi_squared_step`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/ChiSquaredMGF.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Centered chi-squared MGF bound. Let $(\Omega,\mu)$ be a probability space and let $k$ be a positive natural number.
Suppose $Y:\Omega\to\bbr$ is measurable and normally distributed with mean $0$ and
variance $1/k$, that is, its law $Y_*\mu$ equals $N(0,1/k)$. Then for every real $t$
with $\abs{t}\le k/4$, the function $\omega\mapsto \exp\!\bigl(t\,(Y(\omega)^2 -
1/k)\bigr)$ is $\mu$-integrable, and the moment generating function of the centered
variable $Y^2 - 1/k$ satisfies
\[
  \E_\mu\!\left[e^{t(Y^2 - 1/k)}\right] \;\le\; \exp\!\Bigl(\frac{2t^2}{k^2}\Bigr).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- **Centered chi-squared MGF bound.** For a measurable real random variable `Y` on a probability space with law `N(0, 1/k)` (`k > 0`) and every real `t` with `|t| ≤ k/4`, the function `exp(t·(Y² − 1/k))` is integrable and the moment generating function of the centered square `Y² − 1/k` at `t` is at most `exp(2t²/k²)`. This is the single-summand MGF estimate of [DG03, proof of Lemma 2.2], in the sub-exponential form of [Ver18, Lemma 2.7.6] (Gaussian case). Deviation from the sources: the bound is stated with the explicit sub-exponential parameters `(2/k², k/4)` (obtained from the Taylor bound on `|t/k| ≤ 1/4`) rather than DG03's exact optimization of the closed-form MGF. **Proof sketch.** Write `v = 1/k` and `s = t/k`, so `|s| ≤ 1/4` and `2tv = 2s < 1`. Step 1: `exp(t y²)` is integrable against `N(0, v)` (`integrable_exp_mul_sq_gaussianReal_zero`). Step 2 (change of variables): transport this integrability along the law of `Y` to obtain integrability of `exp(t Y²)` on `Ω`, and multiply by the constant `exp(−t/k)` to get integrability of `exp(t(Y² − 1/k))`. Step 3: compute the MGF in closed form: pulling out `exp(−t/k)` and changing variables to the Gaussian integral gives `exp(−t/k) · 1/√(1 − 2s)` by `integral_exp_mul_sq_gaussianReal_zero`. Step 4: write `1/√(1 − 2s) = exp(−½ log(1 − 2s))` and apply the Taylor inequality `−s − ½ log(1 − 2s) ≤ 2s²` (`neg_log_one_sub_two_mul_le_two_sq`) to bound the product by `exp(2s²) = exp(2t²/k²)`. -/
theorem centered_chi_squared_step
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (k : ℕ) (hk : 0 < k)
    (Y : Ω → ℝ) (hY_meas : Measurable Y)
    (hY_law : Measure.map Y μ = gaussianReal 0 ⟨1 / k, by positivity⟩)
    (t : ℝ) (ht : |t| ≤ (k : ℝ) / 4) :
    Integrable (fun ω => Real.exp (t * ((Y ω) ^ 2 - 1 / k))) μ ∧
    mgf (fun ω => (Y ω) ^ 2 - 1 / k) μ t ≤ Real.exp (2 * t ^ 2 / k ^ 2) := by
  -- Setup positivity / range facts.
  have hk_real_pos : (0 : ℝ) < k := by exact_mod_cast hk
  have hk_ne : (k : ℝ) ≠ 0 := hk_real_pos.ne'
  set v : ℝ≥0 := ⟨1 / k, by positivity⟩ with hv_def
  have hv_real : (v : ℝ) = 1 / k := rfl
  have hv_pos : (0 : ℝ) < (v : ℝ) := by rw [hv_real]; positivity
  have hv_ne : v ≠ 0 := fun h => by
    rw [h] at hv_pos
    exact (lt_irrefl 0) (by exact_mod_cast hv_pos)
  -- `2tv < 1`: with `v = 1/k` and `|t| ≤ k/4`, `2tv = 2t/k ≤ 1/2 < 1`.
  have h_2tv_lt : 2 * t * (v : ℝ) < 1 := by
    rw [hv_real]
    have habs : t ≤ k/4 := (abs_le.mp ht).2
    rw [show (2 : ℝ) * t * (1/k) = 2*t/k from by field_simp]
    rw [div_lt_iff₀ hk_real_pos]
    nlinarith
  -- Step 1: `Integrable (exp(t y²)) (gaussianReal 0 v)`.
  have h_int_quad : Integrable (fun y => Real.exp (t * y ^ 2)) (gaussianReal 0 v) :=
    integrable_exp_mul_sq_gaussianReal_zero v hv_ne t h_2tv_lt
  -- Step 2: transfer integrability to Ω via change of variables (using `hY_law`).
  have h_int_pull : Integrable (fun ω => Real.exp (t * (Y ω) ^ 2)) μ := by
    have h_meas_quad : AEStronglyMeasurable
        (fun y : ℝ => Real.exp (t * y ^ 2)) (μ.map Y) := by
      rw [hY_law]; exact h_int_quad.aestronglyMeasurable
    rw [show (fun ω => Real.exp (t * (Y ω) ^ 2)) =
        (fun y : ℝ => Real.exp (t * y ^ 2)) ∘ Y from rfl]
    rw [← MeasureTheory.integrable_map_measure h_meas_quad hY_meas.aemeasurable]
    rw [hY_law]; exact h_int_quad
  -- Multiply by exp(-t/k) to get integrability of `exp(t · (Y² - 1/k))`.
  have h_eq_pointwise : ∀ ω, Real.exp (t * ((Y ω) ^ 2 - 1 / k)) =
      Real.exp (-t / k) * Real.exp (t * (Y ω) ^ 2) := by
    intro ω
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have h_int_centered : Integrable (fun ω => Real.exp (t * ((Y ω) ^ 2 - 1 / k))) μ := by
    have h_int_scaled : Integrable
        (fun ω => Real.exp (-t / k) * Real.exp (t * (Y ω) ^ 2)) μ :=
      h_int_pull.const_mul _
    exact h_int_scaled.congr (ae_of_all _ (fun ω => (h_eq_pointwise ω).symm))
  -- Step 3: compute MGF closed form: `mgf = exp(-t/k) · 1/√(1 - 2t/k)`.
  have h_mgf_eq : mgf (fun ω => (Y ω) ^ 2 - 1 / k) μ t =
      Real.exp (-t / k) * (1 / Real.sqrt (1 - 2 * t * (v : ℝ))) := by
    -- mgf(W) μ t = ∫ exp(t·W) dμ where W = Y² - 1/k.
    rw [mgf]
    -- ∫ exp(t · (Y² - 1/k)) = ∫ exp(-t/k) · exp(t · Y²) = exp(-t/k) · ∫ exp(t · Y²).
    have h_pull_const : (fun ω => Real.exp (t * ((Y ω) ^ 2 - 1 / k))) =
        (fun ω => Real.exp (-t / k) * Real.exp (t * (Y ω) ^ 2)) := by
      funext ω; exact h_eq_pointwise ω
    rw [h_pull_const, integral_const_mul]
    -- Now: exp(-t/k) · ∫ exp(t · Y²) dμ
    -- Pull through Y to get a Gaussian integral.
    have h_change : ∫ ω, Real.exp (t * (Y ω) ^ 2) ∂μ =
        ∫ y, Real.exp (t * y ^ 2) ∂(gaussianReal 0 v) := by
      have h_meas : AEStronglyMeasurable
          (fun y : ℝ => Real.exp (t * y ^ 2)) (μ.map Y) := by
        rw [hY_law]; exact h_int_quad.aestronglyMeasurable
      rw [← hY_law, MeasureTheory.integral_map hY_meas.aemeasurable h_meas]
    rw [h_change, integral_exp_mul_sq_gaussianReal_zero v hv_ne t h_2tv_lt]
  -- Step 4: apply Taylor inequality: `exp(-s) · 1/√(1-2s) ≤ exp(2s²)` for `|s| ≤ 1/4`
  -- (with s = t/k). Setup: s := t/k.
  have hs_abs : |t / k| ≤ 1/4 := by
    rw [abs_div, abs_of_pos hk_real_pos, div_le_iff₀ hk_real_pos]
    have : |t| ≤ k / 4 := ht
    linarith
  have h_pos : 0 < 1 - 2 * (t/k) := by
    have : t / k ≤ 1 / 4 := (abs_le.mp hs_abs).2
    linarith
  have h_sqrt_pos : 0 < Real.sqrt (1 - 2 * (t/k)) := Real.sqrt_pos.mpr h_pos
  -- Taylor bound applied to s = t/k.
  have h_taylor_log : -(t/k) - (1/2) * Real.log (1 - 2 * (t/k)) ≤ 2 * (t/k)^2 :=
    neg_log_one_sub_two_mul_le_two_sq (t/k) hs_abs
  -- Rewrite `1/√(1 - 2s) = exp(-(1/2) log(1 - 2s))` for s = t/k.
  have h_inv_sqrt_exp : (1 : ℝ) / Real.sqrt (1 - 2 * (t/k))
      = Real.exp (-(1/2) * Real.log (1 - 2 * (t/k))) := by
    rw [one_div, Real.sqrt_eq_rpow, Real.rpow_def_of_pos h_pos, ← Real.exp_neg]
    congr 1; ring
  -- The bound: exp(-t/k) · 1/√(1-2(t/k)) ≤ exp(2(t/k)²).
  have h_bound : Real.exp (-t / k) * (1 / Real.sqrt (1 - 2 * (t/k))) ≤
      Real.exp (2 * (t/k)^2) := by
    rw [h_inv_sqrt_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : (-t : ℝ)/k = -(t/k) := by ring
    rw [this]; linarith
  -- Combine integrability and MGF bound.
  refine ⟨h_int_centered, ?_⟩
  rw [h_mgf_eq]
  -- mgf form has `1/√(1 - 2 * t * v)`; we want `1/√(1 - 2 * (t/k))`.
  rw [hv_real, show (2 : ℝ) * t * (1/k) = 2 * (t/k) from by field_simp]
  -- And RHS: `2 * t² / k² = 2 * (t/k)²`.
  rw [show (2 : ℝ) * t ^ 2 / k ^ 2 = 2 * (t/k)^2 from by field_simp]
  exact h_bound
