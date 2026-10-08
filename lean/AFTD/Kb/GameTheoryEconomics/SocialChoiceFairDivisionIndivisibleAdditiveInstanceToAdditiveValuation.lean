import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuation
import AFTD.Kb.Tcs.Weight

/-!
# SocialChoice.FairDivision.Indivisible.AdditiveInstance.toAdditiveValuation

Topic: fair_division   Node: 70fd1a106656

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.AdditiveInstance.toAdditiveValuation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/Instance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The raw additive valuation induced by additive per-item weights.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
/-- The raw additive valuation induced by additive per-item weights. -/
def SocialChoice.FairDivision.Indivisible.AdditiveInstance.toAdditiveValuation {N G : Type*}
    (I : AdditiveInstance N G) : AdditiveValuation N G where
  weight := I.weight
