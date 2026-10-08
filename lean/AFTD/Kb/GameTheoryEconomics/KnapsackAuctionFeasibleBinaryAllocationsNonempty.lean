import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionFeasibleBinaryAllocations
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryRespectsCapacity
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionZeroBinaryRespectsCapacity

/-!
# KnapsackAuction.feasibleBinaryAllocations_nonempty

Topic: mechanism_design   Node: 9ff784e1d083

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.feasibleBinaryAllocations_nonempty`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

KnapsackAuction.feasibleBinaryAllocations_nonempty
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} {U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
variable [Fintype I] [DecidableEq I] in
lemma KnapsackAuction.feasibleBinaryAllocations_nonempty (A : KnapsackAuction I U) (hW : 0 ≤ A.totalCapacity) :
    A.feasibleBinaryAllocations ≠ [] := by
  classical
  intro hnil
  have hmem : (fun _ : I => false) ∈ A.feasibleBinaryAllocations := by
    unfold feasibleBinaryAllocations
    simp [zeroBinaryRespectsCapacity (A := A) hW]
  rw [hnil] at hmem
  simp at hmem
