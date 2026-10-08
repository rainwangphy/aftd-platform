import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuationToValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveInstanceToAdditiveValuation

/-!
# SocialChoice.FairDivision.Indivisible.AdditiveInstance.toValuation

Topic: fair_division   Node: 2e2eda9551cb

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.AdditiveInstance.toValuation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/Instance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The abstract valuation induced by additive per-item weights.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
/-- The abstract valuation induced by additive per-item weights. -/
def SocialChoice.FairDivision.Indivisible.AdditiveInstance.toValuation {N G : Type*}
    (I : AdditiveInstance N G) : Valuation N G :=
  I.toAdditiveValuation.toValuation
