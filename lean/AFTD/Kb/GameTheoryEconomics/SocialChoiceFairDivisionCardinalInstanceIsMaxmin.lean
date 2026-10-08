import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionCardinalInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIsMaxmin
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique

/-!
# SocialChoice.FairDivision.CardinalInstance.IsMaxmin

Topic: fair_division   Node: d07c35fe6f64

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.CardinalInstance.IsMaxmin`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Cardinal.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Maximin optimality for a cardinal instance, using the instance feasibility predicate.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Maximin optimality for a cardinal instance, using the instance feasibility predicate. -/
def SocialChoice.FairDivision.CardinalInstance.IsMaxmin {N R S : Type*} [Fintype N] [Nonempty N]
    (I : CardinalInstance N R S) (A : Allocation N S) : Prop :=
  SocialChoice.FairDivision.IsMaxmin I.feasible I.utility A
