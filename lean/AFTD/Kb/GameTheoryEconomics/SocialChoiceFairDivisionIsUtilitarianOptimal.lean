import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfare

/-!
# SocialChoice.FairDivision.IsUtilitarianOptimal

Topic: fair_division   Node: 8ab5f8906ce1

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.IsUtilitarianOptimal`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Welfare.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Utilitarian optimality: no feasible allocation has larger utilitarian welfare.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
variable {N S : Type*} in
/-- Utilitarian optimality: no feasible allocation has larger utilitarian welfare. -/
def SocialChoice.FairDivision.IsUtilitarianOptimal [Fintype N]
    (feasible : Allocation N S → Prop)
    (u : N → S → ℝ) (A : Allocation N S) : Prop :=
  ∀ B : Allocation N S, feasible B →
    utilitarianWelfare u B ≤ utilitarianWelfare u A
