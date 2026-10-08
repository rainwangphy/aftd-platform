import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityExpSubCgfEq

/-!
# CommunicationComplexity.integrable_exp_sub_cgf

Topic: information   Node: cbda854be18c

Provenance: helper lemma. TCSlib, `CommunicationComplexity.integrable_exp_sub_cgf`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Integrability of the centred exponential moment. Let $(\Omega,\mu)$ be a measure space, let $X\colon\Omega\to\bbr$ be a measurable
function, and let $t\in\bbr$. Write $\Lambda(t)$ for the cumulant generating function of
$X$ under $\mu$, that is, the logarithm of the moment generating function evaluated at
$t$. If the function $x\mapsto e^{t\,X(x)}$ is $\mu$-integrable, then so is the function
$x\mapsto e^{t\,X(x)-\Lambda(t)}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- The exponentially tilted density `exp (t X − cgf_X(t))` is integrable whenever `exp (t X)` is. -/
theorem CommunicationComplexity.integrable_exp_sub_cgf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {t : ℝ} (h_exp_int : Integrable (fun x => Real.exp (t * X x)) μ) :
    Integrable (fun x => Real.exp (t * X x - ProbabilityTheory.cgf X μ t)) μ := by
  rw [exp_sub_cgf_eq]
  exact h_exp_int.const_mul _
