import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuationToValuation

/-!
# SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation_empty

Topic: fair_division   Node: e9be91993ddb

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation_empty`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/Valuation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The value of the empty bundle is zero for additive valuations.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators Finset in
variable {N G : Type*} in
/-- The value of the empty bundle is zero for additive valuations. -/
@[simp]
lemma SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation_empty (w : AdditiveValuation N G) (i : N) :
    w.toValuation.val i ∅ = 0 := by
  simp [toValuation]
