import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation

/-!
# SocialChoice.FairDivision.egalitarianWelfare

Topic: fair_division   Node: 0e08a216ce83

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.egalitarianWelfare`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Welfare.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Egalitarian welfare: the minimum utility among agents.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
variable {N S : Type*} in
/-- Egalitarian welfare: the minimum utility among agents. -/
noncomputable def SocialChoice.FairDivision.egalitarianWelfare [Fintype N] [Nonempty N]
    (u : N → S → ℝ) (A : Allocation N S) : ℝ :=
  Finset.univ.inf' ⟨Classical.arbitrary N, Finset.mem_univ _⟩ (fun i => u i (A i))
