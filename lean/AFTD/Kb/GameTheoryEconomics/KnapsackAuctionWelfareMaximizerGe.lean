import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionFeasibleBinaryAllocations
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinarySocialWelfare
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionWelfareMaximizer
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionExistsWelfareMaximizer

/-!
# KnapsackAuction.welfareMaximizer_ge

Topic: mechanism_design   Node: 34efb39013c5

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.welfareMaximizer_ge`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

KnapsackAuction.welfareMaximizer_ge
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} {U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
variable [Fintype I] [DecidableEq I] in
lemma KnapsackAuction.welfareMaximizer_ge
    (A : KnapsackAuction I U) (b : I → U) (hW : 0 ≤ A.totalCapacity)
    {x : BinaryAllocation I}
    (hx : x ∈ A.feasibleBinaryAllocations) :
    binarySocialWelfare b x ≤ binarySocialWelfare b (A.welfareMaximizer b hW) := by
  exact (Classical.choose_spec (A.exists_welfareMaximizer b hW)).2 x hx
