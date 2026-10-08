import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionCardinalInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionEgalitarianWelfare
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique

/-!
# SocialChoice.FairDivision.CardinalInstance.egalitarianWelfare

Topic: fair_division   Node: 42435b6232ae

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.CardinalInstance.egalitarianWelfare`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Cardinal.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Egalitarian welfare for a cardinal instance.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Egalitarian welfare for a cardinal instance. -/
noncomputable def SocialChoice.FairDivision.CardinalInstance.egalitarianWelfare {N R S : Type*} [Fintype N] [Nonempty N]
    (I : CardinalInstance N R S) (A : Allocation N S) : ℝ :=
  SocialChoice.FairDivision.egalitarianWelfare I.utility A
