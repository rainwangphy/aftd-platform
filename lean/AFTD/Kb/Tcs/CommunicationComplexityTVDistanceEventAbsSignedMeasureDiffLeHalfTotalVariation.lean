import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexitySignedMeasureDiff
import AFTD.Kb.Tcs.CommunicationComplexityTVDistanceHalfTotalVariationRealUnivEqPosPartRealUniv
import AFTD.Kb.Tcs.CommunicationComplexityTVDistanceJordanPosPartRealUnivEqNegPartRealUniv
import AFTD.Kb.Tcs.CommunicationComplexityTVDistanceSignedMeasureApplyEqPosPartSubNegPart

/-!
# CommunicationComplexity.TVDistance.event_abs_signedMeasureDiff_le_half_totalVariation

Topic: information   Node: 8881c89329da

Provenance: helper lemma. TCSlib, `CommunicationComplexity.TVDistance.event_abs_signedMeasureDiff_le_half_totalVariation`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Event probability gap bounded by half the total variation. Let $\mu$ and $\nu$ be probability measures on a measurable space $\Omega$, and let $\mu
- \nu$ denote their signed measure difference. Then for every measurable set $S
\subseteq \Omega$,
\[
  \abs{(\mu - \nu)(S)} \;\le\; \tfrac{1}{2}\, \abs{\mu - \nu}(\Omega),
\]
where $\abs{\mu - \nu}$ is the total variation measure of $\mu - \nu$ and $\abs{\mu -
\nu}(\Omega)$ is its total mass.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
/-- For every measurable event `S`, `|(μ − ν)(S)|` is at most half the total variation mass of `μ − ν`: writing `μ − ν = P − N`, both `P(S)` and `N(S)` lie in `[0, P(Ω)]`. **Proof sketch.** Let `P`, `N` be the Jordan parts of `μ − ν`. (1) `P(Ω) = N(Ω)`, because `μ` and `ν` are both probability measures. (2) By monotonicity and nonnegativity, `P(S)` and `N(S)` both lie in `[0, P(Ω)]`, so `|P(S) − N(S)| ≤ P(Ω)`. (3) Rewrite half the total variation mass as `P(Ω)` and `(μ − ν)(S)` as `P(S) − N(S)`. -/
lemma CommunicationComplexity.TVDistance.event_abs_signedMeasureDiff_le_half_totalVariation
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : {S : Set Ω // MeasurableSet S}) :
    |signedMeasureDiff μ ν (S : Set Ω)| ≤
      (1 / 2 : ℝ) * (signedMeasureDiff μ ν).totalVariation.real Set.univ := by
  let P := (signedMeasureDiff μ ν).toJordanDecomposition.posPart
  let N := (signedMeasureDiff μ ν).toJordanDecomposition.negPart
  -- Step 1: `P(Ω) = N(Ω)`
  have hPN : P.real Set.univ = N.real Set.univ := by
    simpa [P, N] using jordan_posPart_real_univ_eq_negPart_real_univ μ ν
  -- Step 2: `P(S)`, `N(S)` lie in `[0, P(Ω)]`, so `|P(S) − N(S)| ≤ P(Ω)`
  have hPmono : P.real (S : Set Ω) ≤ P.real Set.univ := measureReal_mono (Set.subset_univ _)
  have hNmono : N.real (S : Set Ω) ≤ N.real Set.univ := measureReal_mono (Set.subset_univ _)
  have hPnonneg : 0 ≤ P.real (S : Set Ω) := measureReal_nonneg
  have hNnonneg : 0 ≤ N.real (S : Set Ω) := measureReal_nonneg
  have hbound :
      |P.real (S : Set Ω) - N.real (S : Set Ω)| ≤ P.real Set.univ := by
    rw [abs_le]
    constructor <;> linarith
  -- Step 3: rewrite both sides in terms of `P` and `N`
  rw [half_totalVariation_real_univ_eq_posPart_real_univ μ ν]
  rw [signedMeasure_apply_eq_posPart_sub_negPart (signedMeasureDiff μ ν) S.property]
  simpa [P, N] using hbound
