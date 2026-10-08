import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation

/-!
# SocialChoice.FairDivision.utilitarianWelfare

Topic: fair_division   Node: cbab86f3be19

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.utilitarianWelfare`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Welfare.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Utilitarian welfare: the sum of agents' utilities from their own shares.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
variable {N S : Type*} in
/-- Utilitarian welfare: the sum of agents' utilities from their own shares. -/
noncomputable def SocialChoice.FairDivision.utilitarianWelfare [Fintype N]
    (u : N → S → ℝ) (A : Allocation N S) : ℝ :=
  ∑ i : N, u i (A i)
