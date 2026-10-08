import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleIsAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleAllocation

/-!
# SocialChoice.FairDivision.Divisible.Instance.feasible

Topic: fair_division   Node: 5f16cc11b146

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.Instance.feasible`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Instance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Feasibility for a divisible instance: an allocation is a measurable partition of the cake.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
/-- Feasibility for a divisible instance: an allocation is a measurable partition of the cake. -/
def SocialChoice.FairDivision.Divisible.Instance.feasible {N Ω : Type*} [MeasurableSpace Ω] [Fintype N]
    (_I : Instance N Ω) (A : Allocation N Ω) : Prop :=
  IsAllocation A
