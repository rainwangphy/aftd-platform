import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionCardinalInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfare
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique

/-!
# SocialChoice.FairDivision.CardinalInstance.utilitarianWelfare

Topic: fair_division   Node: d74b68668eca

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.CardinalInstance.utilitarianWelfare`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Cardinal.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Utilitarian welfare for a cardinal instance.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Utilitarian welfare for a cardinal instance. -/
noncomputable def SocialChoice.FairDivision.CardinalInstance.utilitarianWelfare {N R S : Type*} [Fintype N]
    (I : CardinalInstance N R S) (A : Allocation N S) : ℝ :=
  SocialChoice.FairDivision.utilitarianWelfare I.utility A
