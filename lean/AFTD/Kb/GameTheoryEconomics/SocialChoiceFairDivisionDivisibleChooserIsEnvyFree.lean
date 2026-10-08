import AFTD.Prelude
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
# SocialChoice.FairDivision.Divisible.chooser_isEnvyFree

Topic: fair_division   Node: e2df7e9ca671

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.chooser_isEnvyFree`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/CutAndChoose.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**The chooser (agent 1) never envies the cutter**, regardless of the cut point. Since agent 1 selects whichever piece they value more, their own piece is always at least as valuable as the cutter's piece. No fairness condition on the cut is needed. This is the key asymmetry of cut-and-choose: the chooser's guarantee is unconditional; only the cutter's guarantee depends on the cut being fair.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped unitInterval in
/-- **The chooser (agent 1) never envies the cutter**, regardless of the cut point. Since agent 1 selects whichever piece they value more, their own piece is always at least as valuable as the cutter's piece. No fairness condition on the cut is needed. This is the key asymmetry of cut-and-choose: the chooser's guarantee is unconditional; only the cutter's guarantee depends on the cut being fair. -/
theorem SocialChoice.FairDivision.Divisible.chooser_isEnvyFree (μ : Fin 2 → Measure I) (t : I) :
    (MeasureValuation μ).val 1 (cutAndChooseAlloc μ t 0) ≤
    (MeasureValuation μ).val 1 (cutAndChooseAlloc μ t 1) := by
  -- Reduce to μ 1 (if ...) ≤ μ 1 (if ...) via definitional equality
  show μ 1 (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Ioi t else Iic t) ≤
       μ 1 (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Iic t else Ioi t)
  split_ifs with h
  · exact h
  · push_neg at h; exact le_of_lt h
