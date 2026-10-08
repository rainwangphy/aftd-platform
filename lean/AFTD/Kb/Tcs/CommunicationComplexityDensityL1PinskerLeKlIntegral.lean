import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDensityAbsIntegral
import AFTD.Kb.Tcs.CommunicationComplexityHalfDensityAbsIntegralSqLeIntegralKlFunRnDensity
import AFTD.Kb.Tcs.CommunicationComplexityIntegralKlFunRnDerivEqKlIntegral
import AFTD.Kb.Tcs.CommunicationComplexityRnDensity

/-!
# CommunicationComplexity.density_l1_pinsker_le_kl_integral

Topic: information   Node: 6d1d4bb48592

Provenance: helper lemma. TCSlib, `CommunicationComplexity.density_l1_pinsker_le_kl_integral`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Pinsker-type bound via the KL integral. Let $\mu$ and $\nu$ be probability measures on a measurable space $\Omega$ with $\mu$
absolutely continuous with respect to $\nu$, and write $\frac{d\mu}{d\nu}$ for the
(real-valued) Radon–Nikodym density. Suppose the log-likelihood ratio $x \mapsto
\log\frac{d\mu}{d\nu}(x)$ is $\mu$-integrable. Then
\[
\frac{1}{2}\left(\int_{\Omega} \left|\frac{d\mu}{d\nu}(x) - 1\right|\,d\nu(x)\right)^{2}
  \;\le\;
  \int_{\Omega} \log\frac{d\mu}{d\nu}(x)\,d\mu(x),
\]
where the inner integral on the left is the $L^{1}(\nu)$-distance of the density from
the constant $1$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- If `μ ≪ ν` and the log-likelihood ratio is `μ`-integrable, then `½ (∫ |dμ/dν − 1| dν)² ≤ ∫ llr μ ν dμ`. -/
theorem CommunicationComplexity.density_l1_pinsker_le_kl_integral
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν)
    (h_int : Integrable (llr μ ν) μ) :
    (1 / 2 : ℝ) * densityAbsIntegral μ ν ^ 2 ≤
      ∫ x, llr μ ν x ∂μ := by
  calc
    (1 / 2 : ℝ) * densityAbsIntegral μ ν ^ 2
        ≤ ∫ x, InformationTheory.klFun (rnDensity μ ν x) ∂ν :=
      half_densityAbsIntegral_sq_le_integral_klFun_rnDensity μ ν h_ac h_int
    _ = ∫ x, llr μ ν x ∂μ :=
      integral_klFun_rnDeriv_eq_kl_integral μ ν h_ac h_int
