import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCutAndChooseAlloc
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCutAndChooseAllocZero

/-!
# SocialChoice.FairDivision.Divisible.cutAndChooseAlloc_one

Topic: fair_division   Node: e715a661714d

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.cutAndChooseAlloc_one`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/CutAndChoose.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Chooser (agent 1) receives the left piece if they prefer it, the right piece otherwise.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped unitInterval in
/-- Chooser (agent 1) receives the left piece if they prefer it, the right piece otherwise. -/
@[simp]
lemma SocialChoice.FairDivision.Divisible.cutAndChooseAlloc_one (μ : Fin 2 → Measure I) (t : I) :
    cutAndChooseAlloc μ t 1 = if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Iic t else Ioi t := by
  simp [cutAndChooseAlloc]
