import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDensityPositiveIntegral
import AFTD.Kb.Tcs.CommunicationComplexityTvDistanceSupEqDensityPositiveIntegralOfAc
import AFTD.Kb.Tcs.CommunicationComplexityTVDistanceTvDistanceEqTvDistanceSup
import AFTD.Kb.Tcs.CommunicationComplexityTvDistance

/-!
# CommunicationComplexity.tvDistance_eq_densityPositiveIntegral_of_ac

Topic: information   Node: 8951d0160585

Provenance: helper lemma. TCSlib, `CommunicationComplexity.tvDistance_eq_densityPositiveIntegral_of_ac`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Total variation distance as an integral of density excess. Let $\mu$ and $\nu$ be probability measures on a measurable space $\Omega$, and suppose
that $\mu$ is absolutely continuous with respect to $\nu$. Write $\frac{d\mu}{d\nu}$ for
the (real-valued) Radon–Nikodym derivative of $\mu$ with respect to $\nu$. Then the
total variation distance between $\mu$ and $\nu$ equals the excess mass of $\mu$ over
$\nu$ on the region where $\mu$ locally dominates $\nu$:
\[
\tfrac{1}{2}\,\norm{\mu - \nu}_{\mathrm{TV}}
= \int_{\left\{\,x \in \Omega \;:\; \frac{d\mu}{d\nu}(x) \ge 1\,\right\}}
\left(\frac{d\mu}{d\nu}(x) - 1\right)\, d\nu.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- If `μ ≪ ν`, the total variation distance equals the positive part `∫_{dμ/dν ≥ 1} (dμ/dν − 1) dν` of the centred density. -/
theorem CommunicationComplexity.tvDistance_eq_densityPositiveIntegral_of_ac
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν) :
    tvDistance μ ν = densityPositiveIntegral μ ν := by
  rw [TVDistance.tvDistance_eq_tvDistanceSup,
    tvDistanceSup_eq_densityPositiveIntegral_of_ac μ ν h_ac]
