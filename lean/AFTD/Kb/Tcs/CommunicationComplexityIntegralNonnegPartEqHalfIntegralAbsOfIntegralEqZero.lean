import AFTD.Prelude

/-!
# CommunicationComplexity.integral_nonneg_part_eq_half_integral_abs_of_integral_eq_zero

Topic: information   Node: eb51956de255

Provenance: helper lemma. TCSlib, `CommunicationComplexity.integral_nonneg_part_eq_half_integral_abs_of_integral_eq_zero`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Positive part integrates to half the $L^1$ norm at mean zero. Let $\mu$ be a finite measure on a measurable space $\Omega$, and let $g : \Omega \to
\bbr$ be measurable and integrable with mean zero, $\int_\Omega g\,d\mu = 0$. Then the
integral of $g$ over the region where it is nonnegative equals half its $L^1$ norm:
\[
  \int_{\{x\,:\,g(x)\ge 0\}} g(x)\,d\mu \;=\; \tfrac{1}{2}\int_\Omega \abs{g(x)}\,d\mu.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- For an integrable function `g` with mean zero, the integral of `g` over its nonnegative set `{g ≥ 0}` equals half the integral of `|g|`. **Proof sketch.** Split the integrals over `A = {g ≥ 0}` and its complement. Mean zero gives `∫_A g + ∫_{Aᶜ} g = 0`; on `A` we have `|g| = g` and on `Aᶜ` we have `|g| = −g`, so `∫ |g| = ∫_A g − ∫_{Aᶜ} g = 2 ∫_A g`. -/
theorem CommunicationComplexity.integral_nonneg_part_eq_half_integral_abs_of_integral_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {g : Ω → ℝ} (hg_meas : Measurable g) (hg : Integrable g μ)
    (h_mean : ∫ x, g x ∂μ = 0) :
    ∫ x in {x | 0 ≤ g x}, g x ∂μ = (1 / 2 : ℝ) * ∫ x, |g x| ∂μ := by
  let A : Set Ω := {x | 0 ≤ g x}
  have hA : MeasurableSet A := measurableSet_Ici.preimage hg_meas
  have hmean_decomp :
      ∫ x in A, g x ∂μ + ∫ x in Aᶜ, g x ∂μ = 0 := by
    rw [integral_add_compl hA hg, h_mean]
  have h_abs_A :
      ∫ x in A, |g x| ∂μ = ∫ x in A, g x ∂μ := by
    apply setIntegral_congr_fun hA
    intro x hx
    exact abs_of_nonneg hx
  have h_abs_Ac :
      ∫ x in Aᶜ, |g x| ∂μ = -∫ x in Aᶜ, g x ∂μ := by
    calc
      ∫ x in Aᶜ, |g x| ∂μ = ∫ x in Aᶜ, -g x ∂μ := by
        apply setIntegral_congr_fun hA.compl
        intro x hx
        exact abs_of_nonpos (le_of_not_ge hx)
      _ = -∫ x in Aᶜ, g x ∂μ := by
        rw [integral_neg]
  have h_abs_decomp :
      ∫ x, |g x| ∂μ = ∫ x in A, g x ∂μ - ∫ x in Aᶜ, g x ∂μ := by
    rw [← integral_add_compl hA hg.abs, h_abs_A, h_abs_Ac]
    ring
  rw [h_abs_decomp]
  linarith
