import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexitySignedMeasureDiff
import AFTD.Kb.Tcs.CommunicationComplexityTVDistanceSignedMeasureDiffUniv
import AFTD.Kb.Tcs.CommunicationComplexityTVDistanceSignedMeasureApplyEqPosPartSubNegPart

/-!
# CommunicationComplexity.TVDistance.jordan_posPart_real_univ_eq_negPart_real_univ

Topic: information   Node: 315827ea363d

Provenance: helper lemma. TCSlib, `CommunicationComplexity.TVDistance.jordan_posPart_real_univ_eq_negPart_real_univ`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Jordan parts of a probability-measure difference have equal total mass. Let $\mu$ and $\nu$ be probability measures on a measurable space $\Omega$, and let $\mu
- \nu$ be their signed measure difference. Writing $(\mu-\nu)^{+}$ and $(\mu-\nu)^{-}$
for the positive and negative parts of the Jordan decomposition of $\mu - \nu$, the two
parts assign the same total real mass to the whole space:
\[
(\mu-\nu)^{+}(\Omega) = (\mu-\nu)^{-}(\Omega).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
/-- For `μ − ν = P − N` (Jordan decomposition), the positive and negative parts have the same total mass, `P(Ω) = N(Ω)`. -/
lemma CommunicationComplexity.TVDistance.jordan_posPart_real_univ_eq_negPart_real_univ
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (signedMeasureDiff μ ν).toJordanDecomposition.posPart.real Set.univ =
      (signedMeasureDiff μ ν).toJordanDecomposition.negPart.real Set.univ := by
  have h := signedMeasure_apply_eq_posPart_sub_negPart (signedMeasureDiff μ ν) MeasurableSet.univ
  rw [signedMeasureDiff_univ μ ν] at h
  linarith
