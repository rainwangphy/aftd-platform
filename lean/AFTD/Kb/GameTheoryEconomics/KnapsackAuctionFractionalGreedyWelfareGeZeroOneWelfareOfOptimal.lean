import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionFractionalFeasible
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionFractionalSocialWelfare
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionFractionalGreedyAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionMaximalSocialWelfare
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionWelfareMaximizer
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryToAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryToAllocationFractionalFeasibleOfBinaryRespectsCapacity
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryRespectsCapacityOfMemFeasibleBinaryAllocations
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionWelfareMaximizerMemFeasibleBinaryAllocations
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinarySocialWelfare

/-!
# KnapsackAuction.fractionalGreedyWelfare_ge_zeroOneWelfare_of_optimal

Topic: mechanism_design   Node: 71d8e9cdfb0f

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.fractionalGreedyWelfare_ge_zeroOneWelfare_of_optimal`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If the ratio-sorted greedy fractional allocation is optimal for the fractional relaxation, then its welfare dominates the welfare of the optimal `0/1` knapsack allocation. This is the standard relaxation comparison: every feasible binary allocation is also a feasible fractional allocation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} {U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
variable [Fintype I] [DecidableEq I] [LinearOrder I] in
/-- If the ratio-sorted greedy fractional allocation is optimal for the fractional relaxation, then its welfare dominates the welfare of the optimal `0/1` knapsack allocation. This is the standard relaxation comparison: every feasible binary allocation is also a feasible fractional allocation. -/
theorem KnapsackAuction.fractionalGreedyWelfare_ge_zeroOneWelfare_of_optimal
    (A : KnapsackAuction I U) (b : I → U) (hW : 0 ≤ A.totalCapacity)
    (hgreedyOptimal :
      ∀ x : I → U, A.fractionalFeasible x →
        fractionalSocialWelfare b x ≤
          fractionalSocialWelfare b (A.fractionalGreedyAllocation b)) :
    A.maximalSocialWelfare b hW ≤
      fractionalSocialWelfare b (A.fractionalGreedyAllocation b) := by
  let xStar := A.welfareMaximizer b hW
  have hxStarFeas : A.fractionalFeasible (binaryToAllocation xStar) := by
    exact A.binaryToAllocation_fractionalFeasible_of_binaryRespectsCapacity
      (A.BinaryRespectsCapacity_of_mem_feasibleBinaryAllocations
        (A.welfareMaximizer_mem_feasibleBinaryAllocations b hW))
  calc
    A.maximalSocialWelfare b hW
        = fractionalSocialWelfare b (binaryToAllocation xStar) := by
          simp [maximalSocialWelfare, fractionalSocialWelfare, xStar, binarySocialWelfare]
    _ ≤ fractionalSocialWelfare b (A.fractionalGreedyAllocation b) := by
      exact hgreedyOptimal _ hxStarFeas
