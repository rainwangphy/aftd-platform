import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfare

/-!
# SocialChoice.FairDivision.utilitarianWelfare_unique

Topic: fair_division   Node: b5198989949a

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.utilitarianWelfare_unique`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Welfare.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a unique agent, utilitarian welfare is just that agent's utility.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
variable {N S : Type*} in
variable [Fintype N] in
/-- For a unique agent, utilitarian welfare is just that agent's utility. -/
@[simp]
lemma SocialChoice.FairDivision.utilitarianWelfare_unique [Unique N]
    (u : N → S → ℝ) (A : Allocation N S) :
    utilitarianWelfare u A = u default (A default) := by
  simp [utilitarianWelfare]
