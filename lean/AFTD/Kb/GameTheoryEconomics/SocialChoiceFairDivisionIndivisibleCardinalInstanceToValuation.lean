import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleCardinalInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation

/-!
# SocialChoice.FairDivision.Indivisible.CardinalInstance.toValuation

Topic: fair_division   Node: 28a922349b88

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.CardinalInstance.toValuation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/Instance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The raw valuation induced by a cardinal indivisible instance.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
/-- The raw valuation induced by a cardinal indivisible instance. -/
def SocialChoice.FairDivision.Indivisible.CardinalInstance.toValuation {N G : Type*}
    (I : CardinalInstance N G) : Valuation N G where
  val := I.utility
