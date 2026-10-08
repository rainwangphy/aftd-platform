import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCakeValuation

/-!
# SocialChoice.FairDivision.Divisible.IsNormalized

Topic: fair_division   Node: e5d19dc153c7

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.IsNormalized`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Valuation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A normalized cake valuation: each agent values the whole cake at exactly `1`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
/-- A normalized cake valuation: each agent values the whole cake at exactly `1`. -/
def SocialChoice.FairDivision.Divisible.IsNormalized {N Ω V : Type*} [One V] (cv : CakeValuation N Ω V) : Prop :=
  ∀ i : N, cv.val i Set.univ = 1
