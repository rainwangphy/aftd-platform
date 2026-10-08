import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryRespectsCapacity

/-!
# KnapsackAuction.feasibleBinaryAllocations

Topic: mechanism_design   Node: 0b7061ed58ea

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.feasibleBinaryAllocations`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The finite list of binary allocations satisfying the knapsack constraint.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} {U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
variable [Fintype I] [DecidableEq I] in
/-- The finite list of binary allocations satisfying the knapsack constraint. -/
noncomputable def KnapsackAuction.feasibleBinaryAllocations (A : KnapsackAuction I U) : List (BinaryAllocation I) := by
  classical
  exact ((Finset.univ : Finset (BinaryAllocation I)).filter fun x => A.binaryRespectsCapacity x).toList
