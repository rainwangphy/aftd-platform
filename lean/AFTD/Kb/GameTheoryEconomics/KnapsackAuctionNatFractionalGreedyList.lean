import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionDpSolveList
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction

/-!
# KnapsackAuction.natFractionalGreedyList

Topic: mechanism_design   Node: 22077ee009f4

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.natFractionalGreedyList`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fractional greedy prefix algorithm on a natural-number remaining capacity: take each whole item if it fits, and otherwise take exactly the remaining fraction of the current item and halt.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] [LinearOrder I] [Nonempty I] in
/-- Fractional greedy prefix algorithm on a natural-number remaining capacity: take each whole item if it fits, and otherwise take exactly the remaining fraction of the current item and halt. -/
noncomputable def KnapsackAuction.natFractionalGreedyList (w : I → Nat) : List I → Nat → I → ℝ
  | [], _ => fun _ => 0
  | i :: items, remaining =>
      if _ : w i ≤ remaining then
        Function.update (natFractionalGreedyList w items (remaining - w i)) i 1
      else
        fun j => if j = i then (remaining : ℝ) / w i else 0
termination_by items _ => items.length
