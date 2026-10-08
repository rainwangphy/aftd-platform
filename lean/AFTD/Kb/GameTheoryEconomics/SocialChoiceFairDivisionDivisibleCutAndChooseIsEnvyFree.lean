import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleIsFairCutPoint
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleIsEnvyFree
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCutAndChooseAlloc
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCakeValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCutterIsEnvyFreeOfFair
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleChooserIsEnvyFree
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureValuationValEmpty
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCutAndChooseAllocZero
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCutAndChooseAllocOne

/-!
# SocialChoice.FairDivision.Divisible.cutAndChoose_isEnvyFree

Topic: fair_division   Node: 33850545e6f2

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.cutAndChoose_isEnvyFree`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/CutAndChoose.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Both agents are envy-free** at any fair cut point. This combines `chooser_isEnvyFree` (unconditional) and `cutter_isEnvyFree_of_fair` (requires fair cut) to give the full `IsEnvyFree` predicate for both agents.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped unitInterval in
/-- **Both agents are envy-free** at any fair cut point. This combines `chooser_isEnvyFree` (unconditional) and `cutter_isEnvyFree_of_fair` (requires fair cut) to give the full `IsEnvyFree` predicate for both agents. -/
theorem SocialChoice.FairDivision.Divisible.cutAndChoose_isEnvyFree (μ : Fin 2 → Measure I) (t : I)
    (hfair : IsFairCutPoint μ t) :
    IsEnvyFree (MeasureValuation μ) (cutAndChooseAlloc μ t) := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact le_refl _
  · exact cutter_isEnvyFree_of_fair μ t hfair
  · exact chooser_isEnvyFree μ t
  · exact le_refl _
