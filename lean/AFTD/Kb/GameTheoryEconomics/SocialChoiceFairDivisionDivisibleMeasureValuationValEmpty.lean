import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCakeValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureValuation

/-!
# SocialChoice.FairDivision.Divisible.MeasureValuation.val_empty

Topic: fair_division   Node: 3afb678c8bb5

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.MeasureValuation.val_empty`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Valuation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The value of the empty piece is zero.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
variable {N Ω : Type*} [MeasurableSpace Ω] (μ : N → MeasureTheory.Measure Ω) in
/-- The value of the empty piece is zero. -/
@[simp]
lemma SocialChoice.FairDivision.Divisible.MeasureValuation.val_empty (i : N) : (MeasureValuation μ).val i ∅ = 0 :=
  MeasureTheory.measure_empty
