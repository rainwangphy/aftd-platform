import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCardinalInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionCardinalInstanceUtilitarianWelfare
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCardinalInstanceToGenericCardinalInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique

/-!
# SocialChoice.FairDivision.Divisible.CardinalInstance.utilitarianWelfare

Topic: fair_division   Node: fb8604b8b9cd

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.CardinalInstance.utilitarianWelfare`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Instance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Utilitarian welfare for a divisible cardinal instance.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
/-- Utilitarian welfare for a divisible cardinal instance. -/
noncomputable def SocialChoice.FairDivision.Divisible.CardinalInstance.utilitarianWelfare {N Ω : Type*}
    [MeasurableSpace Ω] [Fintype N]
    (I : CardinalInstance N Ω) (A : Allocation N Ω) : ℝ :=
  SocialChoice.FairDivision.CardinalInstance.utilitarianWelfare
    I.toGenericCardinalInstance A
