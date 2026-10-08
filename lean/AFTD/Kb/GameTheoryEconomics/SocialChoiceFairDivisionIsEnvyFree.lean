import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation

/-!
# SocialChoice.FairDivision.IsEnvyFree

Topic: fair_division   Node: 8bd2e51e9894

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.IsEnvyFree`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Fairness.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Envy-free: every agent weakly prefers their own share to every other agent's share.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N S : Type*} in
/-- Envy-free: every agent weakly prefers their own share to every other agent's share. -/
def SocialChoice.FairDivision.IsEnvyFree
    (u : N → S → ℝ) (A : Allocation N S) : Prop :=
  ∀ i j : N, u i (A j) ≤ u i (A i)
