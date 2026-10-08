import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCardinalInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionCardinalInstanceIsParetoOptimal
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCardinalInstanceToGenericCardinalInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique

/-!
# SocialChoice.FairDivision.Divisible.CardinalInstance.IsParetoOptimal

Topic: fair_division   Node: 613cfa6a7864

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.CardinalInstance.IsParetoOptimal`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Instance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Pareto optimality for a divisible cardinal instance.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
/-- Pareto optimality for a divisible cardinal instance. -/
def SocialChoice.FairDivision.Divisible.CardinalInstance.IsParetoOptimal {N Ω : Type*} [MeasurableSpace Ω] [Fintype N]
    (I : CardinalInstance N Ω) (A : Allocation N Ω) : Prop :=
  SocialChoice.FairDivision.CardinalInstance.IsParetoOptimal
    I.toGenericCardinalInstance A
