import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleIsAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureInstanceIsEnvyFree
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureInstanceIsProportional
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleIsEnvyFreeIsProportional
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureValuationValEmpty

/-!
# SocialChoice.FairDivision.Divisible.MeasureInstance.IsEnvyFree.isProportional

Topic: fair_division   Node: 9e41cc7ad974

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.MeasureInstance.IsEnvyFree.isProportional`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Instance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Envy-freeness implies proportionality for complete measure-based divisible allocations.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
/-- Envy-freeness implies proportionality for complete measure-based divisible allocations. -/
theorem SocialChoice.FairDivision.Divisible.MeasureInstance.IsEnvyFree.isProportional {N Ω : Type*}
    [MeasurableSpace Ω] [Fintype N]
    (I : MeasureInstance N Ω)
    (A : Allocation N Ω)
    (ha : IsAllocation A)
    (hef : I.IsEnvyFree A) :
    I.IsProportional (Fintype.card N) A :=
  SocialChoice.FairDivision.Divisible.IsEnvyFree.isProportional I.measure A ha hef
