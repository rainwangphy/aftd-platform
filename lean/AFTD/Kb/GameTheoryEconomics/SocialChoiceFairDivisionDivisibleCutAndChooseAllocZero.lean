import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCutAndChooseAlloc
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique

/-!
# SocialChoice.FairDivision.Divisible.cutAndChooseAlloc_zero

Topic: fair_division   Node: 10a6f5fe8d22

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.cutAndChooseAlloc_zero`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/CutAndChoose.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cutter (agent 0) receives the right piece when the chooser prefers left, and the left piece otherwise.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped unitInterval in
/-- Cutter (agent 0) receives the right piece when the chooser prefers left, and the left piece otherwise. -/
@[simp]
lemma SocialChoice.FairDivision.Divisible.cutAndChooseAlloc_zero (μ : Fin 2 → Measure I) (t : I) :
    cutAndChooseAlloc μ t 0 = if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Ioi t else Iic t := rfl
