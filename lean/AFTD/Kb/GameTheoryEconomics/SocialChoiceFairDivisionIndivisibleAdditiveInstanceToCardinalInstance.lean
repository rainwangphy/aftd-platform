import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleCardinalInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveInstanceToValuation

/-!
# SocialChoice.FairDivision.Indivisible.AdditiveInstance.toCardinalInstance

Topic: fair_division   Node: c1880f7b95ea

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.AdditiveInstance.toCardinalInstance`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/Instance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The cardinal instance induced by additive per-item weights.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
/-- The cardinal instance induced by additive per-item weights. -/
def SocialChoice.FairDivision.Indivisible.AdditiveInstance.toCardinalInstance {N G : Type*}
    (I : AdditiveInstance N G) : CardinalInstance N G where
  allGoods := I.allGoods
  utility := I.toValuation.val
