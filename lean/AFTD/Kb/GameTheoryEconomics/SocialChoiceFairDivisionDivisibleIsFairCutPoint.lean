import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCutAndChooseAlloc
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique

/-!
# SocialChoice.FairDivision.Divisible.IsFairCutPoint

Topic: fair_division   Node: db1d9a2bfe64

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.IsFairCutPoint`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/CutAndChoose.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A cut point `t` is **fair** (for the cutter, agent 0) if agent 0's measure is split equally: `μ 0 [0, t] = μ 0 (t, 1]`. At a fair cut the cutter is indifferent between the two halves, so they cannot envy whichever piece the chooser selects.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped unitInterval in
/-- A cut point `t` is **fair** (for the cutter, agent 0) if agent 0's measure is split equally: `μ 0 [0, t] = μ 0 (t, 1]`. At a fair cut the cutter is indifferent between the two halves, so they cannot envy whichever piece the chooser selects. -/
noncomputable def SocialChoice.FairDivision.Divisible.IsFairCutPoint (μ : Fin 2 → Measure I) (t : I) : Prop :=
  μ 0 (Iic t) = μ 0 (Ioi t)
