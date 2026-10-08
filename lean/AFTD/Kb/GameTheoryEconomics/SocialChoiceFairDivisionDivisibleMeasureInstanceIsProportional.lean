import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleIsProportional
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureInstanceToCakeValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureValuationValEmpty

/-!
# SocialChoice.FairDivision.Divisible.MeasureInstance.IsProportional

Topic: fair_division   Node: 655a0c6c8ee2

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.MeasureInstance.IsProportional`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Instance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Proportionality for a measure-based divisible instance, stated in `ENNReal`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
/-- Proportionality for a measure-based divisible instance, stated in `ENNReal`. -/
def SocialChoice.FairDivision.Divisible.MeasureInstance.IsProportional {N Ω : Type*} [MeasurableSpace Ω]
    (I : MeasureInstance N Ω) (n : ℕ) (A : Allocation N Ω) : Prop :=
  SocialChoice.FairDivision.Divisible.IsProportional n I.toCakeValuation A
