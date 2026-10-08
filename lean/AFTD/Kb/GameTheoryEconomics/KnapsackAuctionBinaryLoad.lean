import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryToAllocation

/-!
# KnapsackAuction.binaryLoad

Topic: mechanism_design   Node: 36b18403c5c0

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.binaryLoad`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The weighted load induced by a binary allocation profile.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} {U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
variable [Fintype I] [DecidableEq I] in
/-- The weighted load induced by a binary allocation profile. -/
def KnapsackAuction.binaryLoad (A : KnapsackAuction I U) (x : BinaryAllocation I) : U :=
  ∑ i, A.weight i * binaryToAllocation x i
