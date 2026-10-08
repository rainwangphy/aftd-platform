import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionWelfareMaximizingAllocationRule
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismMyersonPayment

/-!
# KnapsackAuction.welfareMaximizingPaymentRule

Topic: mechanism_design   Node: bf890827b5e3

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.welfareMaximizingPaymentRule`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Myerson payment formula associated with the welfare-maximizing knapsack allocation rule.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] in
/-- The Myerson payment formula associated with the welfare-maximizing knapsack allocation rule. -/
noncomputable def KnapsackAuction.welfareMaximizingPaymentRule
    (A : KnapsackAuction I ℝ) (hW : 0 ≤ A.totalCapacity) : (I → ℝ) → I → ℝ :=
  SingleParameterMechanism.myersonPayment (A.welfareMaximizingAllocationRule hW)
