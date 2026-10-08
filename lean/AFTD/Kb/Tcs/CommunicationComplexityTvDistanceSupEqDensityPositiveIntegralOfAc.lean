import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDensityPositiveIntegral
import AFTD.Kb.Tcs.CommunicationComplexityDensityPositiveSet
import AFTD.Kb.Tcs.CommunicationComplexityIntegrableRnDensitySubOne
import AFTD.Kb.Tcs.CommunicationComplexityIntegralRnDensitySubOneEqZeroOfAc
import AFTD.Kb.Tcs.CommunicationComplexityMeasurableRnDensity
import AFTD.Kb.Tcs.CommunicationComplexityMeasureRealSubEqSetIntegralRnDensitySubOne
import AFTD.Kb.Tcs.CommunicationComplexityRnDensity
import AFTD.Kb.Tcs.CommunicationComplexitySSupAbsSetIntegralEqNonnegPartOfIntegralEqZero
import AFTD.Kb.Tcs.CommunicationComplexityTvDistanceSup
import AFTD.Kb.Tcs.G

/-!
# CommunicationComplexity.tvDistanceSup_eq_densityPositiveIntegral_of_ac

Topic: information   Node: 012101a2a172

Provenance: helper lemma. TCSlib, `CommunicationComplexity.tvDistanceSup_eq_densityPositiveIntegral_of_ac`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Total variation distance as the excess-mass integral. Let $\mu$ and $\nu$ be probability measures on a measurable space $\Omega$, and suppose
$\mu$ is absolutely continuous with respect to $\nu$. Write $\frac{d\mu}{d\nu}$ for the
Radon–Nikodym derivative of $\mu$ with respect to $\nu$. Then the total variation
distance, taken as the supremum
\[
\mathrm{TV}_{\sup}(\mu,\nu) = \sup\bigl\{\,\abs{\mu(S) - \nu(S)} : S \subseteq \Omega
\text{ measurable}\,\bigr\},
\]
equals the excess mass of $\mu$ over $\nu$ on the region where $\mu$ locally dominates:
\[
\mathrm{TV}_{\sup}(\mu,\nu) = \int_{\{x\,:\,\frac{d\mu}{d\nu}(x)\,\ge\,1\}}
\left(\frac{d\mu}{d\nu}(x) - 1\right)\,d\nu(x).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- If `μ ≪ ν`, the supremum form of the total variation distance equals the positive part `∫_{dμ/dν ≥ 1} (dμ/dν − 1) dν` of the centred density. **Proof sketch.** By `measureReal_sub_eq_setIntegral_rnDensity_sub_one` the family of values `|μ(S) − ν(S)|` over measurable `S` coincides with the family `|∫_S (dμ/dν − 1) dν|`; since the centred density is integrable with mean zero, the supremum of the latter is its positive part (`sSup_abs_setIntegral_eq_nonneg_part_of_integral_eq_zero`). -/
theorem CommunicationComplexity.tvDistanceSup_eq_densityPositiveIntegral_of_ac
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν) :
    tvDistanceSup μ ν = densityPositiveIntegral μ ν := by
  rw [tvDistanceSup]
  have h_range :
      (Set.range fun S : {S : Set Ω // MeasurableSet S} =>
        |μ.real (S : Set Ω) - ν.real (S : Set Ω)|) =
      (Set.range fun S : {S : Set Ω // MeasurableSet S} =>
        |∫ x in (S : Set Ω), (rnDensity μ ν x - 1) ∂ν|) := by
    ext r
    constructor
    · rintro ⟨S, rfl⟩
      refine ⟨S, ?_⟩
      change |∫ x in (S : Set Ω), (rnDensity μ ν x - 1) ∂ν| =
        |μ.real (S : Set Ω) - ν.real (S : Set Ω)|
      rw [← measureReal_sub_eq_setIntegral_rnDensity_sub_one μ ν h_ac (S : Set Ω)]
    · rintro ⟨S, rfl⟩
      refine ⟨S, ?_⟩
      change |μ.real (S : Set Ω) - ν.real (S : Set Ω)| =
        |∫ x in (S : Set Ω), (rnDensity μ ν x - 1) ∂ν|
      rw [measureReal_sub_eq_setIntegral_rnDensity_sub_one μ ν h_ac (S : Set Ω)]
  rw [h_range]
  have hsup :=
    sSup_abs_setIntegral_eq_nonneg_part_of_integral_eq_zero
      (μ := ν) (g := fun x => rnDensity μ ν x - 1)
      ((measurable_rnDensity μ ν).sub measurable_const)
      (integrable_rnDensity_sub_one μ ν)
      (integral_rnDensity_sub_one_eq_zero_of_ac μ ν h_ac)
  simpa [densityPositiveIntegral, densityPositiveSet, sub_nonneg] using hsup
