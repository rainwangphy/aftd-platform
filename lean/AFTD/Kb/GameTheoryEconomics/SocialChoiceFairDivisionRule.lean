import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation

/-!
# SocialChoice.FairDivision.Rule

Topic: fair_division   Node: 05ba87fa497c

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Rule`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A fair-division rule returns a feasible allocation for every instance.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A fair-division rule returns a feasible allocation for every instance. -/
def SocialChoice.FairDivision.Rule (N R S : Type*) :=
  (I : Instance N R S) → {A : Allocation N S // I.feasible A}
