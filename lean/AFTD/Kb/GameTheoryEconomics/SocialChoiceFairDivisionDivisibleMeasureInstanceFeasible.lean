import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleIsAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique

/-!
# SocialChoice.FairDivision.Divisible.MeasureInstance.feasible

Topic: fair_division   Node: d23b55d5d31f

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.MeasureInstance.feasible`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Instance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Feasibility for a measure-based divisible instance. Like the ordinal and cardinal divisible cases, this depends only on the ambient cake: a feasible allocation is a measurable partition of `Set.univ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
/-- Feasibility for a measure-based divisible instance. Like the ordinal and cardinal divisible cases, this depends only on the ambient cake: a feasible allocation is a measurable partition of `Set.univ`. -/
def SocialChoice.FairDivision.Divisible.MeasureInstance.feasible {N Ω : Type*} [MeasurableSpace Ω] [Fintype N]
    (_I : MeasureInstance N Ω) (A : Allocation N Ω) : Prop :=
  IsAllocation A
