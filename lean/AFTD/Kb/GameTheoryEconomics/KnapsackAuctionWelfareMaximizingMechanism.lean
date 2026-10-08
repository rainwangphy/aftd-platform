import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionWelfareMaximizingAllocationRule
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionWelfareMaximizingPaymentRule

/-!
# KnapsackAuction.welfareMaximizingMechanism

Topic: mechanism_design   Node: ebfd39cad007

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.welfareMaximizingMechanism`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The canonical welfare-maximizing single-parameter knapsack mechanism, with payments given by the Myerson formula.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] in
/-- The canonical welfare-maximizing single-parameter knapsack mechanism, with payments given by the Myerson formula. -/
noncomputable def KnapsackAuction.welfareMaximizingMechanism
    (A : KnapsackAuction I ℝ) (hW : 0 ≤ A.totalCapacity) : SingleParameterMechanism I ℝ where
  allocationRule := A.welfareMaximizingAllocationRule hW
  paymentRule := A.welfareMaximizingPaymentRule hW
