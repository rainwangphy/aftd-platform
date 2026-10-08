import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexitySignedMeasureDiff

/-!
# CommunicationComplexity.TVDistance.signedMeasureDiff_univ

Topic: information   Node: 64e2c6454f4e

Provenance: helper lemma. TCSlib, `CommunicationComplexity.TVDistance.signedMeasureDiff_univ`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Signed measure difference vanishes on the whole space. Let $\mu$ and $\nu$ be probability measures on a measurable space $\Omega$, and let $\mu
- \nu$ denote their signed measure difference. Then $(\mu - \nu)(\Omega) = 0$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
/-- The signed measure `μ − ν` of two probability measures gives the whole space mass `0`. -/
lemma CommunicationComplexity.TVDistance.signedMeasureDiff_univ
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    signedMeasureDiff μ ν Set.univ = 0 := by
  rw [signedMeasureDiff, Measure.toSignedMeasure_sub_apply MeasurableSet.univ]
  simp
