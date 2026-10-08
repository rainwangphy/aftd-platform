import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplus
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAllocationRule
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionWinningVirtualValue
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusLeWinningVirtualValue
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusVirtualSurplusMaximizingAllocationRuleEqOfPos
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusNonposOfWinningVirtualValueNonpos
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusVirtualSurplusMaximizingAllocationRuleEqZeroOfNotPos
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfileSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfileOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionUpdateReportProfileSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileSplitMeasurableEquivApplyFst
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileSplitMeasurableEquivApplySnd
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileSplitMeasurableEquivSymmApply
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionExpectedSellerRevenueInEnvironmentSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingMechanismAllocationRule
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingMechanismPaymentRule
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAuctionAllocationRule
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAuctionPaymentRule
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAuctionPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAuctionOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAuctionTypeData
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAuctionToSingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAuctionToDirectBayesianMechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProductPriorIsProbabilityMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionOpponentProductPriorIsProbabilityMeasure

/-!
# BayesianSingleItemAuction.virtualSurplus_le_virtualSurplusMaximizingAllocationRule

Topic: mechanism_design   Node: 4ed4d32489ec

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.virtualSurplus_le_virtualSurplusMaximizingAllocationRule`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/OptimalSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Pointwise virtual-surplus maximality.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open scoped BigOperators in
open MeasureTheory in
variable {I : Type*} in
/-- Pointwise virtual-surplus maximality. -/
theorem BayesianSingleItemAuction.virtualSurplus_le_virtualSurplusMaximizingAllocationRule
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {x : (I → ℝ) → I → ℝ} {b : I → ℝ}
    (hx_nonneg : ∀ i, 0 ≤ x b i)
    (hx_capacity : (∑ i, x b i) ≤ 1) :
    A.virtualSurplus x b ≤
    A.virtualSurplus A.virtualSurplusMaximizingAllocationRule b := by
  by_cases hpos : 0 < A.winningVirtualValue b
  · have hle := A.virtualSurplus_le_winningVirtualValue hx_nonneg hx_capacity (le_of_lt hpos)
    simpa [A.virtualSurplus_virtualSurplusMaximizingAllocationRule_eq_of_pos b hpos] using hle
  · have hle := A.virtualSurplus_nonpos_of_winningVirtualValue_nonpos hx_nonneg (le_of_not_gt hpos)
    simpa [A.virtualSurplus_virtualSurplusMaximizingAllocationRule_eq_zero_of_not_pos b hpos]
      using hle
