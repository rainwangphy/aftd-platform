import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDensityAbsIntegral
import AFTD.Kb.Tcs.CommunicationComplexityHalfIntegralAbsSubOneSqLeIntegralKlFun
import AFTD.Kb.Tcs.CommunicationComplexityIntegrableRnDensity
import AFTD.Kb.Tcs.CommunicationComplexityIntegralRnDensityEqOneOfAc
import AFTD.Kb.Tcs.CommunicationComplexityMeasurableRnDensity
import AFTD.Kb.Tcs.CommunicationComplexityRnDensity
import AFTD.Kb.Tcs.CommunicationComplexityRnDensityNonneg

/-!
# CommunicationComplexity.half_densityAbsIntegral_sq_le_integral_klFun_rnDensity

Topic: information   Node: 0eadcc34c875

Provenance: helper lemma. TCSlib, `CommunicationComplexity.half_densityAbsIntegral_sq_le_integral_klFun_rnDensity`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A Pinsker-type inequality for the Radon–Nikodym density. Let $\mu$ and $\nu$ be probability measures on a measurable space $\Omega$ with $\mu$
absolutely continuous with respect to $\nu$, and write $f = \frac{d\mu}{d\nu}$ for the
(real-valued) Radon–Nikodym density. Suppose the log-likelihood ratio $x \mapsto
\log\frac{d\mu}{d\nu}(x)$ is $\mu$-integrable. Then
\[
  \frac{1}{2}\left(\int_\Omega \abs{f(x) - 1}\,d\nu(x)\right)^{2}
  \;\le\;
  \int_\Omega \bigl(f(x)\log f(x) - f(x) + 1\bigr)\,d\nu(x),
\]
where the left-hand inner integral is the $L^1(\nu)$-distance of the density from $1$
and the right-hand integrand is the Kullback–Leibler integrand $t \mapsto t\log t - t +
1$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- If `μ ≪ ν` and the log-likelihood ratio is `μ`-integrable, then `½ (∫ |dμ/dν − 1| dν)² ≤ ∫ klFun (dμ/dν) dν`; this is `half_integral_abs_sub_one_sq_le_integral_klFun` applied to the density `dμ/dν`. -/
theorem CommunicationComplexity.half_densityAbsIntegral_sq_le_integral_klFun_rnDensity
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν)
    (h_int : Integrable (llr μ ν) μ) :
    (1 / 2 : ℝ) * densityAbsIntegral μ ν ^ 2 ≤
      ∫ x, InformationTheory.klFun (rnDensity μ ν x) ∂ν := by
  have h_kl_int :
      Integrable (fun x => InformationTheory.klFun (rnDensity μ ν x)) ν := by
    simpa [rnDensity] using
      (InformationTheory.integrable_klFun_rnDeriv_iff
        (μ := μ) (ν := ν) h_ac).2 h_int
  simpa [densityAbsIntegral] using
    half_integral_abs_sub_one_sq_le_integral_klFun
      (μ := ν) (f := rnDensity μ ν)
      (measurable_rnDensity μ ν) (integrable_rnDensity μ ν) h_kl_int
      (rnDensity_nonneg μ ν) (integral_rnDensity_eq_one_of_ac μ ν h_ac)
