import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation

/-!
# SocialChoice.FairDivision.IsProportional

Topic: fair_division   Node: 04191e77df3f

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.IsProportional`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Fairness.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Proportional: each agent values their share at least `1 / n` of a distinguished whole share, stated without division.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N S : Type*} in
/-- Proportional: each agent values their share at least `1 / n` of a distinguished whole share, stated without division. -/
def SocialChoice.FairDivision.IsProportional (n : ℕ)
    (whole : S) (u : N → S → ℝ) (A : Allocation N S) : Prop :=
  ∀ i : N, u i whole ≤ (n : ℝ) * u i (A i)
