import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionEgalitarianWelfare

/-!
# SocialChoice.FairDivision.IsMaxmin

Topic: fair_division   Node: 8abca0807d45

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.IsMaxmin`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Welfare.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Maximin optimality: no feasible allocation has larger egalitarian welfare.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
variable {N S : Type*} in
/-- Maximin optimality: no feasible allocation has larger egalitarian welfare. -/
def SocialChoice.FairDivision.IsMaxmin [Fintype N] [Nonempty N]
    (feasible : Allocation N S → Prop)
    (u : N → S → ℝ) (A : Allocation N S) : Prop :=
  ∀ B : Allocation N S, feasible B →
    egalitarianWelfare u B ≤ egalitarianWelfare u A
