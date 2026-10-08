import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityIntegrableRnDensity
import AFTD.Kb.Tcs.CommunicationComplexityIntegralRnDensityEqOneOfAc
import AFTD.Kb.Tcs.CommunicationComplexityRnDensity

/-!
# CommunicationComplexity.integral_rnDensity_sub_one_eq_zero_of_ac

Topic: information   Node: cd29c5cdf5bf

Provenance: helper lemma. TCSlib, `CommunicationComplexity.integral_rnDensity_sub_one_eq_zero_of_ac`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Mean of the Radon–Nikodym density minus one vanishes. Let $\mu$ and $\nu$ be probability measures on a measurable space $\Omega$, and suppose
that $\mu$ is absolutely continuous with respect to $\nu$. Writing $\frac{d\mu}{d\nu}$
for the Radon–Nikodym density of $\mu$ with respect to $\nu$ (the real-valued version of
the Radon–Nikodym derivative), one has \[ \int_{\Omega} \left(\frac{d\mu}{d\nu}(x) -
1\right)\, d\nu(x) = 0. \]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- If `μ ≪ ν` then the centred density `dμ/dν − 1` has `ν`-mean zero. -/
theorem CommunicationComplexity.integral_rnDensity_sub_one_eq_zero_of_ac
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν) :
    ∫ x, rnDensity μ ν x - 1 ∂ν = 0 := by
  rw [integral_sub (integrable_rnDensity μ ν) (integrable_const 1),
    integral_rnDensity_eq_one_of_ac μ ν h_ac]
  simp
