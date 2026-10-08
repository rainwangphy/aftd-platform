import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryRespectsCapacity
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryLoad
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryToAllocation

/-!
# KnapsackAuction.zeroBinaryRespectsCapacity

Topic: mechanism_design   Node: f1337ada716f

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.zeroBinaryRespectsCapacity`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

KnapsackAuction.zeroBinaryRespectsCapacity
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} {U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
variable [Fintype I] [DecidableEq I] in
omit [DecidableEq I] in
lemma KnapsackAuction.zeroBinaryRespectsCapacity (A : KnapsackAuction I U) (hW : 0 ≤ A.totalCapacity) :
    A.binaryRespectsCapacity (fun _ => false) := by
  simp [binaryRespectsCapacity, binaryLoad, binaryToAllocation, hW]
