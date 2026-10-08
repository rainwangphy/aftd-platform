import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionSortedAgentsByRatio
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionFractionalGreedyList

/-!
# KnapsackAuction.fractionalGreedyAllocation

Topic: mechanism_design   Node: 0613e3334149

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.fractionalGreedyAllocation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The greedy fractional knapsack allocation obtained by sorting agents by value-to-weight ratio and then filling capacity in that order.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} {U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
variable [Fintype I] [DecidableEq I] [LinearOrder I] in
/-- The greedy fractional knapsack allocation obtained by sorting agents by value-to-weight ratio and then filling capacity in that order. -/
noncomputable def KnapsackAuction.fractionalGreedyAllocation
    (A : KnapsackAuction I U) (b : I → U) : I → U :=
  A.fractionalGreedyList b (A.sortedAgentsByRatio b) A.totalCapacity
