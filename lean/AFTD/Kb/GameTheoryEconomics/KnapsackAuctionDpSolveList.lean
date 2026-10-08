import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionNatBinarySocialWelfare
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionCapacity

/-!
# KnapsackAuction.dpSolveList

Topic: mechanism_design   Node: 838e1781feb5

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.dpSolveList`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A computable dynamic-programming solver for finite `0/1` knapsack instances. The solver processes the agents in the given list order and uses the standard "skip or take" recursion on the remaining capacity. This is the algorithmic counterpart to the abstract welfare-maximizer above, specialized to natural weights, natural capacity, and natural reported values.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] in
/-- A computable dynamic-programming solver for finite `0/1` knapsack instances. The solver processes the agents in the given list order and uses the standard "skip or take" recursion on the remaining capacity. This is the algorithmic counterpart to the abstract welfare-maximizer above, specialized to natural weights, natural capacity, and natural reported values. -/
def KnapsackAuction.dpSolveList (w b : I → Nat) : List I → Nat → BinaryAllocation I
  | [], _ => fun _ => false
  | i :: is, capacity =>
      if w i ≤ capacity then
        let skip := dpSolveList w b is capacity
        let takeTail := dpSolveList w b is (capacity - w i)
        let take := Function.update takeTail i true
        if natBinarySocialWelfare b take ≥ natBinarySocialWelfare b skip then
          take
        else
          skip
      else
        dpSolveList w b is capacity
termination_by items _ => items.length
