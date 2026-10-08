import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation

/-!
# SocialChoice.FairDivision.IsEquitable

Topic: fair_division   Node: e028becb2ae4

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.IsEquitable`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Fairness.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Equitable: all agents obtain the same utility from their own shares.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N S : Type*} in
/-- Equitable: all agents obtain the same utility from their own shares. -/
def SocialChoice.FairDivision.IsEquitable (u : N → S → ℝ) (A : Allocation N S) : Prop :=
  ∀ i j : N, u i (A i) = u j (A j)
