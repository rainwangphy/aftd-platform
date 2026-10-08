import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsMonotone
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionWelfareMaximizingAllocationRule
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionWelfareMaximizingPaymentRule
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryToAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionWelfareMaximizer
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinaryAllocation
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionFeasibleBinaryAllocations
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionWelfareMaximizerMemFeasibleBinaryAllocations
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinarySocialWelfare
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionWelfareMaximizerGe
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinarySocialWelfareUpdate

/-!
# KnapsackAuction.welfareMaximizingAllocationRule_isMonotone

Topic: mechanism_design   Node: 4c1b19284d9a

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.welfareMaximizingAllocationRule_isMonotone`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

KnapsackAuction.welfareMaximizingAllocationRule_isMonotone
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] in
lemma KnapsackAuction.welfareMaximizingAllocationRule_isMonotone
    (A : KnapsackAuction I ℝ) (hW : 0 ≤ A.totalCapacity) :
    SingleParameterMechanism.IsMonotone
      ({ allocationRule := A.welfareMaximizingAllocationRule hW
         paymentRule := A.welfareMaximizingPaymentRule hW } :
        SingleParameterMechanism I ℝ) := by
  intro i θ θ' hθ b
  by_cases hEq : θ = θ'
  · simp [welfareMaximizingAllocationRule, hEq]
  · have hlt : θ < θ' := lt_of_le_of_ne hθ hEq
    let bLo := Function.update b i θ
    let bHi := Function.update b i θ'
    let xLo := A.welfareMaximizer bLo hW
    let xHi := A.welfareMaximizer bHi hW
    have hxLo_feas : xLo ∈ A.feasibleBinaryAllocations := by
      exact A.welfareMaximizer_mem_feasibleBinaryAllocations bLo hW
    have hxHi_feas : xHi ∈ A.feasibleBinaryAllocations := by
      exact A.welfareMaximizer_mem_feasibleBinaryAllocations bHi hW
    have hLo :
        binarySocialWelfare bLo xHi ≤ binarySocialWelfare bLo xLo := by
      exact A.welfareMaximizer_ge bLo hW hxHi_feas
    have hHi :
        binarySocialWelfare bHi xLo ≤ binarySocialWelfare bHi xHi := by
      exact A.welfareMaximizer_ge bHi hW hxLo_feas
    by_cases hxLo_i : xLo i <;> by_cases hxHi_i : xHi i
    · simp [welfareMaximizingAllocationRule, bLo, bHi, xLo, xHi, binaryToAllocation,
        hxLo_i, hxHi_i]
    · exfalso
      have hLo' : binarySocialWelfare bLo xHi - binarySocialWelfare bLo xLo ≤ 0 := by
        linarith
      have hHi' : 0 ≤ binarySocialWelfare bHi xHi - binarySocialWelfare bHi xLo := by
        linarith
      have hHi_eq :
          binarySocialWelfare bHi xHi = binarySocialWelfare bLo xHi := by
        rw [binarySocialWelfare_update (b := b) (i := i) (θ := θ') (x := xHi),
          binarySocialWelfare_update (b := b) (i := i) (θ := θ) (x := xHi)]
        simp [binaryToAllocation, hxHi_i]
      have hLo_eq :
          binarySocialWelfare bHi xLo = binarySocialWelfare bLo xLo + (θ' - θ) := by
        rw [binarySocialWelfare_update (b := b) (i := i) (θ := θ') (x := xLo),
          binarySocialWelfare_update (b := b) (i := i) (θ := θ) (x := xLo)]
        simp [binaryToAllocation, hxLo_i]
        ring
      have : 0 < θ' - θ := sub_pos.mpr hlt
      rw [hHi_eq, hLo_eq] at hHi'
      linarith
    · simp [welfareMaximizingAllocationRule, bLo, bHi, xLo, xHi, binaryToAllocation,
        hxLo_i, hxHi_i]
    · simp [welfareMaximizingAllocationRule, bLo, bHi, xLo, xHi, binaryToAllocation,
        hxLo_i, hxHi_i]
