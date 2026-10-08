import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityRnDensity

/-!
# CommunicationComplexity.integral_klFun_rnDeriv_eq_kl_integral

Topic: information   Node: 143bc7639d5d

Provenance: helper lemma. TCSlib, `CommunicationComplexity.integral_klFun_rnDeriv_eq_kl_integral`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Two integral forms of the Kullback–Leibler divergence. Let $\mu$ and $\nu$ be probability measures on a measurable space $\Omega$ with $\mu$
absolutely continuous with respect to $\nu$, and write $\frac{d\mu}{d\nu}$ for the
(real-valued) Radon–Nikodym density of $\mu$ with respect to $\nu$. Assume that the
log-likelihood ratio $x \mapsto \log\frac{d\mu}{d\nu}(x)$ is $\mu$-integrable. Then
\[
  \int_\Omega \varphi\!\left(\frac{d\mu}{d\nu}(x)\right) d\nu(x)
  \;=\;
  \int_\Omega \log\frac{d\mu}{d\nu}(x)\, d\mu(x),
\]
where $\varphi(t) = t\log t + 1 - t$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- If `μ ≪ ν` and the log-likelihood ratio is `μ`-integrable, then `∫ klFun (dμ/dν) dν = ∫ llr μ ν dμ`, the real-valued KL divergence (Mathlib's `integral_klFun_rnDeriv`). -/
theorem CommunicationComplexity.integral_klFun_rnDeriv_eq_kl_integral
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν)
    (h_int : Integrable (llr μ ν) μ) :
    (∫ x, InformationTheory.klFun (rnDensity μ ν x) ∂ν) =
      ∫ x, llr μ ν x ∂μ := by
  have h := InformationTheory.integral_klFun_rnDeriv h_ac h_int
  simpa [rnDensity] using h
