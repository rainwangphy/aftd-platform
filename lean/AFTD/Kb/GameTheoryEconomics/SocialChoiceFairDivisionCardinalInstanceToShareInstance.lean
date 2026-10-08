import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionCardinalInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionShareInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionCardinalInstanceInducedSharePref
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# SocialChoice.FairDivision.CardinalInstance.toShareInstance

Topic: fair_division   Node: 0cc2782c03b1

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.CardinalInstance.toShareInstance`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Cardinal.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Convert a cardinal instance to the induced ordinal no-externality instance.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Convert a cardinal instance to the induced ordinal no-externality instance. -/
def SocialChoice.FairDivision.CardinalInstance.toShareInstance {N R S : Type*}
    (I : CardinalInstance N R S) : ShareInstance N R S where
  resource := I.resource
  feasible := I.feasible
  sharePref := I.inducedSharePref
