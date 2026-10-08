import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleIsEnvyFree
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureInstanceToCakeValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureValuationValEmpty

/-!
# SocialChoice.FairDivision.Divisible.MeasureInstance.IsEnvyFree

Topic: fair_division   Node: ffe5980113bc

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.MeasureInstance.IsEnvyFree`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Instance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Envy-freeness for a measure-based divisible instance, stated in `ENNReal`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
/-- Envy-freeness for a measure-based divisible instance, stated in `ENNReal`. -/
def SocialChoice.FairDivision.Divisible.MeasureInstance.IsEnvyFree {N Ω : Type*} [MeasurableSpace Ω]
    (I : MeasureInstance N Ω) (A : Allocation N Ω) : Prop :=
  SocialChoice.FairDivision.Divisible.IsEnvyFree I.toCakeValuation A
