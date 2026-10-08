import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCakeValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureValuationValEmpty

/-!
# SocialChoice.FairDivision.Divisible.MeasureValuation.val_iUnion

Topic: fair_division   Node: 46ca3e1e15ab

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.MeasureValuation.val_iUnion`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Valuation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a countably-indexed pairwise-disjoint family of measurable sets, `MeasureValuation` is countably additive (tsum).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
variable {N Ω : Type*} [MeasurableSpace Ω] (μ : N → MeasureTheory.Measure Ω) in
/-- For a countably-indexed pairwise-disjoint family of measurable sets, `MeasureValuation` is countably additive (tsum). -/
lemma SocialChoice.FairDivision.Divisible.MeasureValuation.val_iUnion [Countable N] (i : N) (A : Allocation N Ω)
    (hdisj : ∀ j k : N, j ≠ k → Disjoint (A j) (A k))
    (hmeas : ∀ j, MeasurableSet (A j)) :
    (MeasureValuation μ).val i (⋃ j, A j) = ∑' j, (MeasureValuation μ).val i (A j) :=
  MeasureTheory.measure_iUnion (fun ⦃j k⦄ hjk => hdisj j k hjk) hmeas
