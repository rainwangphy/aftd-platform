import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCakeValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureValuationValEmpty

/-!
# SocialChoice.FairDivision.Divisible.MeasureValuation.val_union

Topic: fair_division   Node: 2982b045722a

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.MeasureValuation.val_union`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Valuation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For disjoint measurable sets, `MeasureValuation` is additive.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
variable {N Ω : Type*} [MeasurableSpace Ω] (μ : N → MeasureTheory.Measure Ω) in
/-- For disjoint measurable sets, `MeasureValuation` is additive. -/
lemma SocialChoice.FairDivision.Divisible.MeasureValuation.val_union (i : N) (S T : Set Ω)
    (hdisj : Disjoint S T) (ht : MeasurableSet T) :
    (MeasureValuation μ).val i (S ∪ T) =
      (MeasureValuation μ).val i S + (MeasureValuation μ).val i T :=
  MeasureTheory.measure_union hdisj ht
