import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexitySignedMeasureDiff
import AFTD.Kb.Tcs.CommunicationComplexityTVDistanceJordanPosPartRealUnivEqNegPartRealUniv
import AFTD.Kb.Tcs.CommunicationComplexityTVDistanceTotalVariationRealUniv

/-!
# CommunicationComplexity.TVDistance.half_totalVariation_real_univ_eq_posPart_real_univ

Topic: information   Node: 66fc446d4ccd

Provenance: helper lemma. TCSlib, `CommunicationComplexity.TVDistance.half_totalVariation_real_univ_eq_posPart_real_univ`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Half the total variation equals the positive Jordan part. Let $\mu$ and $\nu$ be probability measures on a measurable space $\Omega$, and let
$\mu-\nu$ denote their signed measure difference. Writing $\abs{\mu-\nu}$ for its total
variation measure and $(\mu-\nu)^{+}$ for the positive part of its Jordan decomposition,
one has
\[
\tfrac{1}{2}\,\abs{\mu-\nu}(\Omega) = (\mu-\nu)^{+}(\Omega),
\]
where both sides are evaluated as real numbers on the whole space $\Omega$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
/-- Half the total variation mass of `μ − ν` equals the total mass `P(Ω)` of the positive part of its Jordan decomposition. -/
lemma CommunicationComplexity.TVDistance.half_totalVariation_real_univ_eq_posPart_real_univ
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (1 / 2 : ℝ) * (signedMeasureDiff μ ν).totalVariation.real Set.univ =
      (signedMeasureDiff μ ν).toJordanDecomposition.posPart.real Set.univ := by
  rw [totalVariation_real_univ]
  rw [jordan_posPart_real_univ_eq_negPart_real_univ μ ν]
  ring
