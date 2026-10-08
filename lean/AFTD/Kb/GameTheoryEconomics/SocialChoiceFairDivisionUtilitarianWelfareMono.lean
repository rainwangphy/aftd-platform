import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfare

/-!
# SocialChoice.FairDivision.utilitarianWelfare_mono

Topic: fair_division   Node: 31b903b9fa7b

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.utilitarianWelfare_mono`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Welfare.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Utilitarian welfare is monotone: pointwise improvement implies welfare improvement.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
variable {N S : Type*} in
variable [Fintype N] in
/-- Utilitarian welfare is monotone: pointwise improvement implies welfare improvement. -/
lemma SocialChoice.FairDivision.utilitarianWelfare_mono
    (u : N → S → ℝ) (A B : Allocation N S)
    (h : ∀ i : N, u i (A i) ≤ u i (B i)) :
    utilitarianWelfare u A ≤ utilitarianWelfare u B :=
  Finset.sum_le_sum (fun i _ => h i)
