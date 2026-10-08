import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleIsNormalized
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureValuationValEmpty

/-!
# SocialChoice.FairDivision.Divisible.IsNormalized.iff_isProbabilityMeasure

Topic: fair_division   Node: af59d33e1b2e

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.IsNormalized.iff_isProbabilityMeasure`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Valuation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For `MeasureValuation`, normalization is equivalent to every agent's measure being a probability measure.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
/-- For `MeasureValuation`, normalization is equivalent to every agent's measure being a probability measure. -/
lemma SocialChoice.FairDivision.Divisible.IsNormalized.iff_isProbabilityMeasure {N Ω : Type*} [MeasurableSpace Ω]
    (μ : N → MeasureTheory.Measure Ω) :
    IsNormalized (MeasureValuation μ) ↔ ∀ i, MeasureTheory.IsProbabilityMeasure (μ i) := by
  simp only [IsNormalized, MeasureValuation]
  exact ⟨fun h i => ⟨h i⟩, fun h i => (h i).measure_univ⟩
