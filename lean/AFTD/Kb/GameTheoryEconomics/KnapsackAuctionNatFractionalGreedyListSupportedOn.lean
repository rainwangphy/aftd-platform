import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionFractionalSupportedOn
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionNatFractionalGreedyList
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction

/-!
# KnapsackAuction.natFractionalGreedyList_supportedOn

Topic: mechanism_design   Node: e105a319018e

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.natFractionalGreedyList_supportedOn`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

KnapsackAuction.natFractionalGreedyList_supportedOn
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] [LinearOrder I] [Nonempty I] in
omit [Fintype I] [LinearOrder I] [Nonempty I] in
lemma KnapsackAuction.natFractionalGreedyList_supportedOn (w : I → Nat) :
    ∀ items remaining,
      fractionalSupportedOn items (natFractionalGreedyList w items remaining) := by
  intro items
  induction items with
  | nil =>
      intro remaining i hi
      simp [natFractionalGreedyList] at hi
  | cons i items ih =>
      intro remaining j hj
      by_cases hfit : w i ≤ remaining
      · by_cases hji : j = i
        · subst hji
          simp
        · have hjtail : natFractionalGreedyList w items (remaining - w i) j ≠ 0 := by
            simpa [natFractionalGreedyList, hfit, Function.update, hji] using hj
          exact List.mem_cons_of_mem _ (ih _ _ hjtail)
      · by_cases hji : j = i
        · subst hji
          simp
        · exfalso
          simp [natFractionalGreedyList, hfit, hji] at hj
