import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionCardinalInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIsParetoOptimal
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique

/-!
# SocialChoice.FairDivision.CardinalInstance.IsParetoOptimal

Topic: fair_division   Node: ae2cb2def222

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.CardinalInstance.IsParetoOptimal`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Cardinal.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Pareto optimality for a cardinal instance, using the instance feasibility predicate.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Pareto optimality for a cardinal instance, using the instance feasibility predicate. -/
def SocialChoice.FairDivision.CardinalInstance.IsParetoOptimal {N R S : Type*}
    (I : CardinalInstance N R S) (A : Allocation N S) : Prop :=
  SocialChoice.FairDivision.IsParetoOptimal I.feasible I.utility A
