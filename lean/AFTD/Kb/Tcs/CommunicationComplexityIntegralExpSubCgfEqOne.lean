import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityExpSubCgfEq

/-!
# CommunicationComplexity.integral_exp_sub_cgf_eq_one

Topic: information   Node: bb2c929f5a5c

Provenance: helper lemma. TCSlib, `CommunicationComplexity.integral_exp_sub_cgf_eq_one`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Exponential tilting by the cumulant generating function normalises to one. Let $\mu$ be a probability measure on a measurable space $\Omega$, let $X : \Omega \to
\bbr$ be a random variable, and let $t \in \bbr$. Write $\Lambda(t) = \log \int_\Omega
e^{t X(x)}\,d\mu(x)$ for the cumulant generating function of $X$ at $t$. If the function
$x \mapsto e^{t X(x)}$ is $\mu$-integrable, then
\[
\int_\Omega e^{\,t X(x) - \Lambda(t)}\,d\mu(x) = 1.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- The exponentially tilted density `exp (t X − cgf_X(t))` integrates to `1` whenever `exp (t X)` is integrable. -/
theorem CommunicationComplexity.integral_exp_sub_cgf_eq_one
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {t : ℝ} (h_exp_int : Integrable (fun x => Real.exp (t * X x)) μ) :
    ∫ x, Real.exp (t * X x - ProbabilityTheory.cgf X μ t) ∂μ = 1 := by
  rw [exp_sub_cgf_eq, integral_const_mul]
  change Real.exp (-ProbabilityTheory.cgf X μ t) * ProbabilityTheory.mgf X μ t = 1
  rw [← ProbabilityTheory.exp_cgf h_exp_int]
  rw [Real.exp_neg, inv_mul_cancel₀ (Real.exp_ne_zero _)]
