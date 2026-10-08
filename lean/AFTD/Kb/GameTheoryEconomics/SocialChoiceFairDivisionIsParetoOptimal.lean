import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation

/-!
# SocialChoice.FairDivision.IsParetoOptimal

Topic: fair_division   Node: 36fd141136ae

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.IsParetoOptimal`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Fairness.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Pareto optimal: there is no feasible allocation that weakly improves every agent and strictly improves at least one.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N S : Type*} in
/-- Pareto optimal: there is no feasible allocation that weakly improves every agent and strictly improves at least one. -/
def SocialChoice.FairDivision.IsParetoOptimal
    (feasible : Allocation N S → Prop)
    (u : N → S → ℝ) (A : Allocation N S) : Prop :=
  ¬ ∃ B : Allocation N S, feasible B ∧
    (∀ i : N, u i (A i) ≤ u i (B i)) ∧
    (∃ i : N, u i (A i) < u i (B i))
