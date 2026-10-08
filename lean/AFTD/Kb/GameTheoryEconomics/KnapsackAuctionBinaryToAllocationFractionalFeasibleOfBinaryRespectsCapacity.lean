import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryRespectsCapacity
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionFractionalFeasible
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryToAllocation
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryLoad

/-!
# KnapsackAuction.binaryToAllocation_fractionalFeasible_of_binaryRespectsCapacity

Topic: mechanism_design   Node: 027fd6bab5cd

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.binaryToAllocation_fractionalFeasible_of_binaryRespectsCapacity`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

KnapsackAuction.binaryToAllocation_fractionalFeasible_of_binaryRespectsCapacity
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} {U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
variable [Fintype I] [DecidableEq I] [LinearOrder I] in
omit [DecidableEq I] [LinearOrder I] in
lemma KnapsackAuction.binaryToAllocation_fractionalFeasible_of_binaryRespectsCapacity
    (A : KnapsackAuction I U) {x : BinaryAllocation I}
    (hx : A.binaryRespectsCapacity x) :
    A.fractionalFeasible (binaryToAllocation x) := by
  constructor
  · intro i
    by_cases hxi : x i <;> simp [binaryToAllocation, hxi]
  · simpa [binaryRespectsCapacity, binaryLoad, binaryToAllocation] using hx
