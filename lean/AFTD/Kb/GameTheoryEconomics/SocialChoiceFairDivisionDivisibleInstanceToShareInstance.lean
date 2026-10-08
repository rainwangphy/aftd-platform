import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionShareInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleIsAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleInstanceFeasible
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique
import AFTD.Kb.GameTheoryEconomics.SocialChoiceInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionInstance

/-!
# SocialChoice.FairDivision.Divisible.Instance.toShareInstance

Topic: fair_division   Node: ff0151e8849f

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.Instance.toShareInstance`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Instance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

View a divisible ordinal instance as a generic no-externality fair-division share instance. The resource is the whole cake `Set.univ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
/-- View a divisible ordinal instance as a generic no-externality fair-division share instance. The resource is the whole cake `Set.univ`. -/
def SocialChoice.FairDivision.Divisible.Instance.toShareInstance {N Ω : Type*} [MeasurableSpace Ω] [Fintype N]
    (I : Instance N Ω) :
    SocialChoice.FairDivision.ShareInstance N (Set Ω) (Set Ω) where
  resource := Set.univ
  feasible := fun A => IsAllocation A
  sharePref := I.sharePref
