import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionCardinalInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIsProportional
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique

/-!
# SocialChoice.FairDivision.CardinalInstance.IsProportional

Topic: fair_division   Node: 1d44bf8445ca

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.CardinalInstance.IsProportional`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Cardinal.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Proportionality for a cardinal instance, relative to a distinguished whole share and a supplied population size.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Proportionality for a cardinal instance, relative to a distinguished whole share and a supplied population size. -/
def SocialChoice.FairDivision.CardinalInstance.IsProportional {N R S : Type*}
    (I : CardinalInstance N R S) (n : ℕ) (whole : S)
    (A : Allocation N S) : Prop :=
  SocialChoice.FairDivision.IsProportional n whole I.utility A
