import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionEgalitarianWelfare
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfare
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique

/-!
# SocialChoice.FairDivision.nsmul_egalitarianWelfare_le_utilitarianWelfare

Topic: fair_division   Node: 6f9d47bcbe1b

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.nsmul_egalitarianWelfare_le_utilitarianWelfare`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Welfare.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Without division, egalitarian welfare is bounded above by utilitarian welfare multiplied by the number of agents.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
variable {N S : Type*} in
variable [Fintype N] in
/-- Without division, egalitarian welfare is bounded above by utilitarian welfare multiplied by the number of agents. -/
lemma SocialChoice.FairDivision.nsmul_egalitarianWelfare_le_utilitarianWelfare
    [Nonempty N]
    (u : N → S → ℝ) (A : Allocation N S)
    (hle : ∀ i : N, egalitarianWelfare u A ≤ u i (A i)) :
    Fintype.card N • egalitarianWelfare u A ≤ utilitarianWelfare u A := by
  calc Fintype.card N • egalitarianWelfare u A
      = ∑ _i : N, egalitarianWelfare u A := by
          simp [Finset.sum_const, Finset.card_univ]
    _ ≤ ∑ i : N, u i (A i) := Finset.sum_le_sum (fun i _ => hle i)
    _ = utilitarianWelfare u A := rfl
