import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionCardinalInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIsEnvyFree
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique

/-!
# SocialChoice.FairDivision.CardinalInstance.IsEnvyFree

Topic: fair_division   Node: 91eb7128275b

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.CardinalInstance.IsEnvyFree`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Cardinal.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Envy-freeness for a cardinal instance.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Envy-freeness for a cardinal instance. -/
def SocialChoice.FairDivision.CardinalInstance.IsEnvyFree {N R S : Type*}
    (I : CardinalInstance N R S) (A : Allocation N S) : Prop :=
  SocialChoice.FairDivision.IsEnvyFree I.utility A
