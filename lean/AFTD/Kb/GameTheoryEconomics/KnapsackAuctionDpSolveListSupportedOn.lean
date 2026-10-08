import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionSupportedOn
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionDpSolveList
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionNatBinarySocialWelfare
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionCapacity

/-!
# KnapsackAuction.dpSolveList_supportedOn

Topic: mechanism_design   Node: 01dbfc9548f0

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.dpSolveList_supportedOn`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

KnapsackAuction.dpSolveList_supportedOn
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] in
lemma KnapsackAuction.dpSolveList_supportedOn (w b : I → Nat) :
    ∀ items capacity, supportedOn items (dpSolveList w b items capacity) := by
  intro items
  induction items with
  | nil =>
      intro capacity i hi
      simp [dpSolveList] at hi
  | cons i items ih =>
      intro capacity
      by_cases hwi : w i ≤ capacity
      · let skip := dpSolveList w b items capacity
        let takeTail := dpSolveList w b items (capacity - w i)
        let take := Function.update takeTail i true
        by_cases hchoose : natBinarySocialWelfare b take ≥ natBinarySocialWelfare b skip
        · simp [dpSolveList, hwi, skip, takeTail, take, hchoose]
          intro j hj
          by_cases hji : j = i
          · subst hji
            simp
          · exact List.mem_cons.2 (.inr (ih (capacity - w i) j (by simpa [take, Function.update, hji] using hj)))
        · simp [dpSolveList, hwi, skip, takeTail, take, hchoose]
          intro j hj
          exact List.mem_cons.2 (.inr (ih capacity j hj))
      · intro j hj
        have hj' : dpSolveList w b items capacity j = true := by
          simpa [dpSolveList, hwi] using hj
        exact List.mem_cons.2 (.inr ((ih capacity) j hj'))
