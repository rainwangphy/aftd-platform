import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionFeasibleBinaryAllocations
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryRespectsCapacity

/-!
# KnapsackAuction.BinaryRespectsCapacity_of_mem_feasibleBinaryAllocations

Topic: mechanism_design   Node: 5349fd54a897

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.BinaryRespectsCapacity_of_mem_feasibleBinaryAllocations`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

KnapsackAuction.BinaryRespectsCapacity_of_mem_feasibleBinaryAllocations
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} {U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
variable [Fintype I] [DecidableEq I] [LinearOrder I] in
omit [LinearOrder I] in
lemma KnapsackAuction.BinaryRespectsCapacity_of_mem_feasibleBinaryAllocations
    (A : KnapsackAuction I U) {x : BinaryAllocation I}
    (hx : x ∈ A.feasibleBinaryAllocations) :
    A.binaryRespectsCapacity x := by
  classical
  unfold feasibleBinaryAllocations at hx
  simp at hx
  exact hx
