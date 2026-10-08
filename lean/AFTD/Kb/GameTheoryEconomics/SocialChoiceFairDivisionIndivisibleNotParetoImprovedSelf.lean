import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsAllocation

/-!
# SocialChoice.FairDivision.Indivisible.not_paretoImproved_self

Topic: fair_division   Node: 0180dc417df0

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.not_paretoImproved_self`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/Efficiency.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The allocation itself is not a Pareto improvement over itself.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SocialChoice SocialChoice.FairDivision SocialChoice.FairDivision.Indivisible in
variable {N G : Type*} in
variable [Fintype N] [DecidableEq G] in
variable (v : Valuation N G) (allGoods : Finset G) in
/-- The allocation itself is not a Pareto improvement over itself. -/
lemma SocialChoice.FairDivision.Indivisible.not_paretoImproved_self (A : Allocation N G) :
    ¬ (IsAllocation allGoods A ∧ (∀ i, v.val i (A i) ≤ v.val i (A i)) ∧
       ∃ i, v.val i (A i) < v.val i (A i)) := by
  rintro ⟨_, _, i, hi⟩
  exact lt_irrefl _ hi
