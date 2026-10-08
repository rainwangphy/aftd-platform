import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCardinalInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionCardinalInstanceIsEquitable
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCardinalInstanceToGenericCardinalInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique

/-!
# SocialChoice.FairDivision.Divisible.CardinalInstance.IsEquitable

Topic: fair_division   Node: 6f08f8680bb5

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.CardinalInstance.IsEquitable`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Instance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Equitability for a divisible cardinal instance.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
/-- Equitability for a divisible cardinal instance. -/
def SocialChoice.FairDivision.Divisible.CardinalInstance.IsEquitable {N Ω : Type*} [MeasurableSpace Ω] [Fintype N]
    (I : CardinalInstance N Ω) (A : Allocation N Ω) : Prop :=
  SocialChoice.FairDivision.CardinalInstance.IsEquitable
    I.toGenericCardinalInstance A
