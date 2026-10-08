import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionDpSolveList
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction

/-!
# KnapsackAuction.integralGreedyList

Topic: mechanism_design   Node: e4e2012d8b3e

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.integralGreedyList`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The integral greedy prefix algorithm: process items in a fixed order, take each whole item if it fits, and halt when the first item fails to fit.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] [LinearOrder I] [Nonempty I] in
/-- The integral greedy prefix algorithm: process items in a fixed order, take each whole item if it fits, and halt when the first item fails to fit. -/
def KnapsackAuction.integralGreedyList (w : I → Nat) : List I → Nat → BinaryAllocation I
  | [], _ => fun _ => false
  | i :: items, remaining =>
      if w i ≤ remaining then
        Function.update (integralGreedyList w items (remaining - w i)) i true
      else
        fun _ => false
termination_by items _ => items.length
