import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDensityAbsIntegral
import AFTD.Kb.Tcs.CommunicationComplexityDensityPositiveIntegralEqHalfDensityAbsIntegralOfAc
import AFTD.Kb.Tcs.CommunicationComplexityTvDistanceEqDensityPositiveIntegralOfAc
import AFTD.Kb.Tcs.CommunicationComplexityTvDistance

/-!
# CommunicationComplexity.tvDistance_eq_half_densityAbsIntegral_of_ac

Topic: information   Node: 0cad4dbf8ef1

Provenance: helper lemma. TCSlib, `CommunicationComplexity.tvDistance_eq_half_densityAbsIntegral_of_ac`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Total variation distance via the density's L¹-deviation from one. Let $\mu$ and $\nu$ be probability measures on a measurable space $\Omega$, and suppose
that $\mu$ is absolutely continuous with respect to $\nu$. Then the total variation
distance between $\mu$ and $\nu$ equals one half of the density absolute integral, that
is,
\[
\mathrm{TV}(\mu,\nu) = \frac{1}{2}\int_{\Omega} \left| \frac{d\mu}{d\nu}(x) - 1 \right|
\, d\nu(x).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- If `μ ≪ ν`, the total variation distance is half the `L¹` distance of the density from `1`: `TV(μ, ν) = ½ ∫ |dμ/dν − 1| dν`. -/
theorem CommunicationComplexity.tvDistance_eq_half_densityAbsIntegral_of_ac
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν) :
    tvDistance μ ν = (1 / 2 : ℝ) * densityAbsIntegral μ ν := by
  rw [tvDistance_eq_densityPositiveIntegral_of_ac μ ν h_ac,
    densityPositiveIntegral_eq_half_densityAbsIntegral_of_ac μ ν h_ac]
