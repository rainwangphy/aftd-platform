import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique

/-!
# SocialChoice.FairDivision.Divisible.cutAndChooseAlloc

Topic: fair_division   Node: ddee205506bf

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.cutAndChooseAlloc`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/CutAndChoose.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The cut-and-choose allocation at cut point `t ∈ [0,1]`. The chooser (agent 1) receives the half they value more: - If `μ 1 (Iic t) ≥ μ 1 (Ioi t)`, agent 1 takes `[0, t]`; agent 0 gets `(t, 1]`. - Otherwise, agent 1 takes `(t, 1]`; agent 0 gets `[0, t]`. The allocation is noncomputable because measures are noncomputable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped unitInterval in
/-- The cut-and-choose allocation at cut point `t ∈ [0,1]`. The chooser (agent 1) receives the half they value more: - If `μ 1 (Iic t) ≥ μ 1 (Ioi t)`, agent 1 takes `[0, t]`; agent 0 gets `(t, 1]`. - Otherwise, agent 1 takes `(t, 1]`; agent 0 gets `[0, t]`. The allocation is noncomputable because measures are noncomputable. -/
noncomputable def SocialChoice.FairDivision.Divisible.cutAndChooseAlloc (μ : Fin 2 → Measure I) (t : I) :
    Allocation (Fin 2) I :=
  fun i =>
    if μ 1 (Iic t) ≥ μ 1 (Ioi t) then
      -- chooser takes left, cutter takes right
      if i = 0 then Ioi t else Iic t
    else
      -- chooser takes right, cutter takes left
      if i = 0 then Iic t else Ioi t
