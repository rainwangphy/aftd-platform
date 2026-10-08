import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionSupportedOn
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionIntegralGreedyList
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction

/-!
# KnapsackAuction.integralGreedyList_supportedOn

Topic: mechanism_design   Node: 6a16ecdf9d0c

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.integralGreedyList_supportedOn`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

KnapsackAuction.integralGreedyList_supportedOn
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] [LinearOrder I] [Nonempty I] in
omit [Fintype I] [LinearOrder I] [Nonempty I] in
lemma KnapsackAuction.integralGreedyList_supportedOn (w : I → Nat) :
    ∀ items remaining, supportedOn items (integralGreedyList w items remaining) := by
  intro items
  induction items with
  | nil =>
      intro remaining i hi
      simp [integralGreedyList] at hi
  | cons i items ih =>
      intro remaining j hj
      by_cases hfit : w i ≤ remaining
      · by_cases hji : j = i
        · subst hji
          simp
        · have hjtail : integralGreedyList w items (remaining - w i) j = true := by
            simpa [integralGreedyList, hfit, Function.update, hji] using hj
          exact List.mem_cons_of_mem _ (ih _ _ hjtail)
      · simp [integralGreedyList, hfit] at hj
