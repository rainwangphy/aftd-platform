import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDensityPositiveSet
import AFTD.Kb.Tcs.CommunicationComplexityRnDensity
import AFTD.Kb.Tcs.CommunicationComplexityMeasurableRnDensity
import AFTD.Kb.Tcs.CommunicationComplexityIntegrableRnDensitySubOne
import AFTD.Kb.Tcs.CommunicationComplexityDensityPositiveIntegral
import AFTD.Kb.Tcs.CommunicationComplexityDensityAbsIntegral
import AFTD.Kb.Tcs.CommunicationComplexityIntegralRnDensitySubOneEqZeroOfAc
import AFTD.Kb.Tcs.CommunicationComplexityIntegralNonnegPartEqHalfIntegralAbsOfIntegralEqZero

/-!
# CommunicationComplexity.densityPositiveIntegral_eq_half_densityAbsIntegral_of_ac

Topic: information   Node: b3039489c59e

Provenance: helper lemma. TCSlib, `CommunicationComplexity.densityPositiveIntegral_eq_half_densityAbsIntegral_of_ac`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Positive part equals half the total variation of the density. Let $\mu$ and $\nu$ be probability measures on a measurable space $\Omega$, with $\mu$
absolutely continuous with respect to $\nu$, and write $\frac{d\mu}{d\nu}$ for the
Radon–Nikodym density of $\mu$ with respect to $\nu$. Then the excess mass of the
density above $1$, integrated over the region where the density is at least $1$, equals
half the $L^1(\nu)$-distance of the density from $1$:
\[
\int_{\{x\,:\,\frac{d\mu}{d\nu}(x)\,\ge\,1\}}
\left(\frac{d\mu}{d\nu}(x)-1\right)\,d\nu(x) \;=\; \frac{1}{2}\int_{\Omega}
\left|\frac{d\mu}{d\nu}(x)-1\right|\,d\nu(x).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- If `μ ≪ ν`, the positive part of the centred density is half its `L¹` norm: `∫_{dμ/dν ≥ 1} (dμ/dν − 1) dν = ½ ∫ |dμ/dν − 1| dν`. -/
theorem CommunicationComplexity.densityPositiveIntegral_eq_half_densityAbsIntegral_of_ac
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν) :
    densityPositiveIntegral μ ν = (1 / 2 : ℝ) * densityAbsIntegral μ ν := by
  have h :=
    integral_nonneg_part_eq_half_integral_abs_of_integral_eq_zero
      (μ := ν) (g := fun x => rnDensity μ ν x - 1)
      ((measurable_rnDensity μ ν).sub measurable_const)
      (integrable_rnDensity_sub_one μ ν)
      (integral_rnDensity_sub_one_eq_zero_of_ac μ ν h_ac)
  simpa [densityPositiveIntegral, densityAbsIntegral, densityPositiveSet, sub_nonneg] using h
