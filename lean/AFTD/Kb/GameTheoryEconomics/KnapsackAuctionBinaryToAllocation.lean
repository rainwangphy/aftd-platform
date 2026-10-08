import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryAllocation

/-!
# KnapsackAuction.binaryToAllocation

Topic: mechanism_design   Node: 4ca3b5ad8197

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.binaryToAllocation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The `0/1` allocation vector associated with a binary allocation profile.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I : Type*} {U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
variable [Fintype I] [DecidableEq I] in
/-- The `0/1` allocation vector associated with a binary allocation profile. -/
def KnapsackAuction.binaryToAllocation (x : BinaryAllocation I) : I → U :=
  fun i => if x i then 1 else 0
