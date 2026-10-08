import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryToAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionWelfareMaximizer

/-!
# KnapsackAuction.welfareMaximizingAllocationRule

Topic: mechanism_design   Node: 5243c00ea7a9

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.welfareMaximizingAllocationRule`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The welfare-maximizing allocation rule for the knapsack auction, obtained by choosing a feasible binary allocation with maximal social welfare and then viewing it as an `I → ℝ` allocation vector.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] in
/-- The welfare-maximizing allocation rule for the knapsack auction, obtained by choosing a feasible binary allocation with maximal social welfare and then viewing it as an `I → ℝ` allocation vector. -/
noncomputable def KnapsackAuction.welfareMaximizingAllocationRule
    (A : KnapsackAuction I ℝ) (hW : 0 ≤ A.totalCapacity) : (I → ℝ) → I → ℝ :=
  fun b => binaryToAllocation (A.welfareMaximizer b hW)
