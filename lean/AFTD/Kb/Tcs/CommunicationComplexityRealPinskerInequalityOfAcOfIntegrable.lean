import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDensityAbsIntegral
import AFTD.Kb.Tcs.CommunicationComplexityDensityL1PinskerLeKlIntegral
import AFTD.Kb.Tcs.CommunicationComplexityTvDistanceEqHalfDensityAbsIntegralOfAc
import AFTD.Kb.Tcs.CommunicationComplexityTvDistance

/-!
# CommunicationComplexity.real_pinsker_inequality_of_ac_of_integrable

Topic: information   Node: 1b8d195cc800

Provenance: helper lemma. TCSlib, `CommunicationComplexity.real_pinsker_inequality_of_ac_of_integrable`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Pinsker's inequality under absolute continuity. Let $\mu$ and $\nu$ be probability measures on a measurable space $\Omega$, and write
$\mathrm{TV}(\mu,\nu)$ for their total variation distance. Suppose $\mu$ is absolutely
continuous with respect to $\nu$, and that the log-likelihood ratio $x \mapsto
\log\frac{d\mu}{d\nu}(x)$ is $\mu$-integrable. Then
\[
  2\,\mathrm{TV}(\mu,\nu)^2 \;\le\; \int_\Omega \log\frac{d\mu}{d\nu}(x)\,d\mu(x),
\]
the right-hand side being the Kullback–Leibler divergence of $\mu$ from $\nu$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- Real-valued Pinsker inequality under `μ ≪ ν` and integrability of the log-likelihood ratio: `2 · TV(μ, ν)² ≤ ∫ llr μ ν dμ`. -/
theorem CommunicationComplexity.real_pinsker_inequality_of_ac_of_integrable
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν)
    (h_int : Integrable (llr μ ν) μ) :
    2 * tvDistance μ ν ^ 2 ≤
      ∫ x, llr μ ν x ∂μ := by
  have h_tv := tvDistance_eq_half_densityAbsIntegral_of_ac μ ν h_ac
  have h_l1 := density_l1_pinsker_le_kl_integral μ ν h_ac h_int
  calc
    2 * tvDistance μ ν ^ 2 = (1 / 2 : ℝ) * densityAbsIntegral μ ν ^ 2 := by
      rw [h_tv]
      ring
    _ ≤ ∫ x, llr μ ν x ∂μ := h_l1
