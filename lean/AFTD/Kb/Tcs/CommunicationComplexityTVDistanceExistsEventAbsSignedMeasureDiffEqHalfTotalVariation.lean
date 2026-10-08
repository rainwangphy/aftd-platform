import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexitySignedMeasureDiff
import AFTD.Kb.Tcs.CommunicationComplexityTVDistanceHalfTotalVariationRealUnivEqPosPartRealUniv
import AFTD.Kb.Tcs.CommunicationComplexityTVDistanceSignedMeasureApplyEqPosPartSubNegPart

/-!
# CommunicationComplexity.TVDistance.exists_event_abs_signedMeasureDiff_eq_half_totalVariation

Topic: information   Node: 201f7976a7b2

Provenance: helper lemma. TCSlib, `CommunicationComplexity.TVDistance.exists_event_abs_signedMeasureDiff_eq_half_totalVariation`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Attainment of half the total variation by a single event. Let $\mu$ and $\nu$ be probability measures on a measurable space $\Omega$, and let $\mu
- \nu$ denote their signed measure difference. Then there exists a measurable set $S
\subseteq \Omega$ at which
\[
\abs{(\mu - \nu)(S)} = \tfrac{1}{2}\,\abs{\mu - \nu}(\Omega),
\]
where $\abs{\mu - \nu}$ is the total variation measure of $\mu - \nu$; that is, some
event realizes exactly half the total variation of $\mu - \nu$ over the whole space.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
/-- Some measurable event attains half the total variation mass of `μ − ν`: the complement of a Hahn-decomposition negative set, on which `N` vanishes and `P` has full mass. **Proof sketch.** Take a measurable set `S` from the Hahn decomposition of `μ − ν` such that the positive part `P` vanishes on `S` and the negative part `N` vanishes on `Sᶜ`; the event is `Sᶜ`. (1) Since `P(S) = 0`, `P(Sᶜ) = P(Ω)`. (2) `N(Sᶜ) = 0`. (3) Hence `(μ − ν)(Sᶜ) = P(Sᶜ) − N(Sᶜ) = P(Ω) ≥ 0`, which is half the total variation mass. -/
lemma CommunicationComplexity.TVDistance.exists_event_abs_signedMeasureDiff_eq_half_totalVariation
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∃ S : {S : Set Ω // MeasurableSet S},
      |signedMeasureDiff μ ν (S : Set Ω)| =
        (1 / 2 : ℝ) * (signedMeasureDiff μ ν).totalVariation.real Set.univ := by
  let s := signedMeasureDiff μ ν
  obtain ⟨S, hS, -, -, hPzero, hNzero⟩ :=
    s.toJordanDecomposition.exists_compl_positive_negative
  refine ⟨⟨Sᶜ, hS.compl⟩, ?_⟩
  let P := s.toJordanDecomposition.posPart
  let N := s.toJordanDecomposition.negPart
  -- Step 1: `P(S) = 0`, so `P(Sᶜ) = P(Ω)`
  have hPzero_real : P.real S = 0 := by
    rw [measureReal_def, show P S = 0 by simpa [P] using hPzero, ENNReal.toReal_zero]
  have hPcompl : P.real Sᶜ = P.real Set.univ := by
    rw [measureReal_compl hS, hPzero_real]
    ring
  -- Step 2: `N(Sᶜ) = 0`
  have hNcompl : N.real Sᶜ = 0 := by
    rw [measureReal_def, hNzero, ENNReal.toReal_zero]
  have hnonneg : 0 ≤ P.real Set.univ := measureReal_nonneg
  -- Step 3: `(μ − ν)(Sᶜ) = P(Ω)`, the half total variation
  rw [signedMeasure_apply_eq_posPart_sub_negPart s hS.compl]
  rw [half_totalVariation_real_univ_eq_posPart_real_univ μ ν]
  simp [s, P, N, hPcompl, hNcompl, abs_of_nonneg hnonneg]
