import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCardinalInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionShareInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionCardinalInstanceToShareInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCardinalInstanceToGenericCardinalInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# SocialChoice.FairDivision.Divisible.CardinalInstance.toShareInstance

Topic: fair_division   Node: abbe1439fe62

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.CardinalInstance.toShareInstance`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Instance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

View a divisible cardinal instance as the induced generic ordinal no-externality instance.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
/-- View a divisible cardinal instance as the induced generic ordinal no-externality instance. -/
def SocialChoice.FairDivision.Divisible.CardinalInstance.toShareInstance {N Ω : Type*} [MeasurableSpace Ω] [Fintype N]
    (I : CardinalInstance N Ω) :
    SocialChoice.FairDivision.ShareInstance N (Set Ω) (Set Ω) :=
  I.toGenericCardinalInstance.toShareInstance
