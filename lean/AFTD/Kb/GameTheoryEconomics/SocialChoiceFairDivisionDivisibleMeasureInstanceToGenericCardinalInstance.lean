import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionCardinalInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCardinalInstanceToGenericCardinalInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureInstanceToCardinalInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique

/-!
# SocialChoice.FairDivision.Divisible.MeasureInstance.toGenericCardinalInstance

Topic: fair_division   Node: 3fc617171c71

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.MeasureInstance.toGenericCardinalInstance`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Instance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

View a measure instance as a generic real-valued cardinal fair-division instance.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
/-- View a measure instance as a generic real-valued cardinal fair-division instance. -/
noncomputable def SocialChoice.FairDivision.Divisible.MeasureInstance.toGenericCardinalInstance {N Ω : Type*}
    [MeasurableSpace Ω] [Fintype N]
    (I : MeasureInstance N Ω) :
    SocialChoice.FairDivision.CardinalInstance N (Set Ω) (Set Ω) :=
  I.toCardinalInstance.toGenericCardinalInstance
