import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionEgalitarianWelfare
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique

/-!
# SocialChoice.FairDivision.egalitarianWelfare_le

Topic: fair_division   Node: 99edf50a5240

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.egalitarianWelfare_le`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Welfare.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Egalitarian welfare is bounded above by each agent's utility.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
variable {N S : Type*} in
variable [Fintype N] in
/-- Egalitarian welfare is bounded above by each agent's utility. -/
lemma SocialChoice.FairDivision.egalitarianWelfare_le [Nonempty N]
    (u : N → S → ℝ) (A : Allocation N S) (i : N) :
    egalitarianWelfare u A ≤ u i (A i) :=
  Finset.inf'_le _ (Finset.mem_univ i)
