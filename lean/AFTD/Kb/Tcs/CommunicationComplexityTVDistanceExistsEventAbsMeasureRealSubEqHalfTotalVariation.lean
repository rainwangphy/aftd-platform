import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexitySignedMeasureDiff
import AFTD.Kb.Tcs.CommunicationComplexityTVDistanceExistsEventAbsSignedMeasureDiffEqHalfTotalVariation

/-!
# CommunicationComplexity.TVDistance.exists_event_abs_measureReal_sub_eq_half_totalVariation

Topic: information   Node: dd9139efa2f8

Provenance: helper lemma. TCSlib, `CommunicationComplexity.TVDistance.exists_event_abs_measureReal_sub_eq_half_totalVariation`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Attainment of the total-variation distance. Let $\mu$ and $\nu$ be probability measures on a measurable space $\Omega$, and let $\mu
- \nu$ denote their signed measure difference, with total variation measure
$\abs{\mu-\nu}$. Then there exists a measurable set $S \subseteq \Omega$ such that
\[
  \abs{\mu(S) - \nu(S)} = \tfrac{1}{2}\,\abs{\mu-\nu}(\Omega).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
/-- Some measurable event `S` satisfies `|μ(S) − ν(S)| = ½ ‖μ − ν‖`. -/
lemma CommunicationComplexity.TVDistance.exists_event_abs_measureReal_sub_eq_half_totalVariation
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∃ S : {S : Set Ω // MeasurableSet S},
      |μ.real (S : Set Ω) - ν.real (S : Set Ω)| =
        (1 / 2 : ℝ) * (signedMeasureDiff μ ν).totalVariation.real Set.univ := by
  obtain ⟨S, hS⟩ := exists_event_abs_signedMeasureDiff_eq_half_totalVariation μ ν
  refine ⟨S, ?_⟩
  rw [← Measure.toSignedMeasure_sub_apply S.property]
  simpa [signedMeasureDiff] using hS
