import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleIsFairCutPoint
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCakeValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCutAndChooseAlloc
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureValuationValEmpty
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCutAndChooseAllocZero
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCutAndChooseAllocOne

/-!
# SocialChoice.FairDivision.Divisible.cutter_isEnvyFree_of_fair

Topic: fair_division   Node: 2fb41b4db799

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.cutter_isEnvyFree_of_fair`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/CutAndChoose.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**The cutter (agent 0) does not envy the chooser** at a fair cut. If the cut point `t` satisfies `IsFairCutPoint μ t`, then agent 0 values both halves equally. Regardless of which half the chooser takes, the cutter is indifferent.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped unitInterval in
/-- **The cutter (agent 0) does not envy the chooser** at a fair cut. If the cut point `t` satisfies `IsFairCutPoint μ t`, then agent 0 values both halves equally. Regardless of which half the chooser takes, the cutter is indifferent. -/
theorem SocialChoice.FairDivision.Divisible.cutter_isEnvyFree_of_fair (μ : Fin 2 → Measure I) (t : I)
    (hfair : IsFairCutPoint μ t) :
    (MeasureValuation μ).val 0 (cutAndChooseAlloc μ t 1) ≤
    (MeasureValuation μ).val 0 (cutAndChooseAlloc μ t 0) := by
  show μ 0 (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Iic t else Ioi t) ≤
       μ 0 (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Ioi t else Iic t)
  split_ifs with h
  · -- chooser gets Iic, cutter gets Ioi; need μ 0 (Iic t) ≤ μ 0 (Ioi t)
    exact le_of_eq hfair
  · -- chooser gets Ioi, cutter gets Iic; need μ 0 (Ioi t) ≤ μ 0 (Iic t)
    exact le_of_eq hfair.symm
