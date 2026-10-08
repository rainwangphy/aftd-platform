import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityPinskerInequalityOfAc
import AFTD.Kb.Tcs.CommunicationComplexityTvDistance

/-!
# CommunicationComplexity.pinsker_inequality

Topic: information   Node: db1485fb06fb

Provenance: formalization of a published result. Source: Pinsker's inequality, as formalized in TCSlib (`CommunicationComplexity.pinsker_inequality`). Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Pinsker's inequality. Let $\mu$ and $\nu$ be probability measures on a measurable space $\Omega$, and let
$\mathrm{TV}(\mu,\nu)$ denote their total variation distance and
$\mathrm{KL}(\mu\,\|\,\nu)$ their Kullback–Leibler divergence. Then
\[
  2\,\mathrm{TV}(\mu,\nu)^2 \;\le\; \mathrm{KL}(\mu\,\|\,\nu),
\]
where the left-hand side is regarded as an element of the extended nonnegative reals
$[0,\infty]$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- Pinsker's inequality: for probability measures `μ`, `ν` on any measurable space, `2 · TV(μ, ν)² ≤ KL(μ ‖ ν)`, stated in `ℝ≥0∞` with Mathlib's KL divergence. [RY20, Lemma 6.6] (Pinsker's inequality). Deviation: RY state `D(p‖q) ≥ (2 / ln 2) |p − q|²` with the divergence in bits; here the divergence uses the natural logarithm, so the constant is `2`, the inequality lives in `ℝ≥0∞` (it is trivial when the divergence is infinite), and the measures are arbitrary probability measures rather than distributions on a finite set. The proof route also differs from RY's reduction to the two-point case via the chain rule; see below. **Proof sketch.** The body only dispatches the degenerate cases; the argument lives in the private lemmas of this file. Step 1 (reductions): if `μ` is not absolutely continuous with respect to `ν`, or the log-likelihood ratio is not `μ`-integrable, the divergence is `∞` and there is nothing to prove (`pinsker_inequality_of_ac`, `pinsker_inequality_of_ac_of_integrable`). Step 2 (total variation as an `L¹` norm): with `f = dμ/dν`, the supremum form of the total variation distance is `sup_S |∫_S (f − 1) dν|`, which for a mean-zero integrand is its positive part `∫_{f ≥ 1} (f − 1) dν`, and that is `½ ∫ |f − 1| dν` (`tvDistanceSup_eq_densityPositiveIntegral_of_ac`, `densityPositiveIntegral_eq_half_densityAbsIntegral_of_ac`). Step 3 (sub-Gaussian bound): let `s = sign (f − 1)`, `X = s − E[s]` and `L = ∫ |f − 1| dν`. Then `X` is centred with values in an interval of length `2`, so by Hoeffding's lemma `cgf_X(t) ≤ t²/2`; moreover `∫ f X dν = L`. Step 4 (variational bound): from the pointwise inequality `u y ≤ klFun u + eʸ − 1` one gets `t ∫ f X dν ≤ ∫ klFun (f) dν + cgf_X(t)` for every `t` (`variational_integral_mul_le_integral_klFun_add_cgf`); taking `t = L` and using Step 3 gives `½ L² ≤ ∫ klFun (f) dν` (`half_integral_abs_sub_one_sq_le_integral_klFun`). Step 5 (identify the divergence): `∫ klFun (f) dν = ∫ llr μ ν dμ = KL(μ ‖ ν)` by Mathlib's `integral_klFun_rnDeriv`; combining with Step 2, `2 · TV² = ½ L² ≤ KL(μ ‖ ν)`. -/
theorem CommunicationComplexity.pinsker_inequality
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ENNReal.ofReal (2 * tvDistance μ ν ^ 2) ≤
      InformationTheory.klDiv μ ν := by
  by_cases h_ac : μ ≪ ν
  · exact pinsker_inequality_of_ac μ ν h_ac
  · rw [InformationTheory.klDiv_of_not_ac h_ac]
    exact le_top
