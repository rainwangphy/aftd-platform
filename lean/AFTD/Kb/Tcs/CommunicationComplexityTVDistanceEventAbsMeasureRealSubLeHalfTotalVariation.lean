import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexitySignedMeasureDiff
import AFTD.Kb.Tcs.CommunicationComplexityTVDistanceEventAbsSignedMeasureDiffLeHalfTotalVariation

/-!
# CommunicationComplexity.TVDistance.event_abs_measureReal_sub_le_half_totalVariation

Topic: information   Node: 709b4f458385

Provenance: helper lemma. TCSlib, `CommunicationComplexity.TVDistance.event_abs_measureReal_sub_le_half_totalVariation`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Probability gap bounded by half total variation. Let $\mu$ and $\nu$ be probability measures on a measurable space $\Omega$, and let $\mu
- \nu$ denote their signed measure difference. Then for every measurable set $S
\subseteq \Omega$,
\[
\abs{\mu(S) - \nu(S)} \le \tfrac{1}{2}\,\abs{\mu - \nu}(\Omega),
\]
where $\abs{\mu - \nu}$ is the total variation measure of $\mu - \nu$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
/-- For every measurable event `S`, `|μ(S) − ν(S)|` is at most half the total variation mass of `μ − ν`. -/
lemma CommunicationComplexity.TVDistance.event_abs_measureReal_sub_le_half_totalVariation
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : {S : Set Ω // MeasurableSet S}) :
    |μ.real (S : Set Ω) - ν.real (S : Set Ω)| ≤
      (1 / 2 : ℝ) * (signedMeasureDiff μ ν).totalVariation.real Set.univ := by
  rw [← Measure.toSignedMeasure_sub_apply S.property]
  simpa [signedMeasureDiff] using event_abs_signedMeasureDiff_le_half_totalVariation μ ν S
