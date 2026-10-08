import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCakeValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleAllocation
import AFTD.Kb.Tcs.V

/-!
# SocialChoice.FairDivision.Divisible.IsEquitable

Topic: fair_division   Node: 474f2c991b36

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.IsEquitable`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Equitable: every agent assigns exactly the same value to their own piece.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
/-- Equitable: every agent assigns exactly the same value to their own piece. -/
def SocialChoice.FairDivision.Divisible.IsEquitable {N Ω V : Type*} [Preorder V]
    (cv : CakeValuation N Ω V) (A : Allocation N Ω) : Prop :=
  ∀ i j : N, cv.val i (A i) = cv.val j (A j)
