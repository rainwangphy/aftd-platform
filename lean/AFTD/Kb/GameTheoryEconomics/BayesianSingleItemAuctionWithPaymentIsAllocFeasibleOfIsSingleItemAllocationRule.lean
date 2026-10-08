import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIsSingleItemAllocationRule
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsAllocFeasible
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIsSingleItemAllocationRuleLeOne
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfileSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfileOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionUpdateReportProfileSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileSplitMeasurableEquivApplyFst
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileSplitMeasurableEquivApplySnd
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileSplitMeasurableEquivSymmApply
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionExpectedSellerRevenueInEnvironmentSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProductPriorIsProbabilityMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionOpponentProductPriorIsProbabilityMeasure

/-!
# BayesianSingleItemAuction.withPayment_isAllocFeasible_of_isSingleItemAllocationRule

Topic: mechanism_design   Node: f8d94b15ac04

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.withPayment_isAllocFeasible_of_isSingleItemAllocationRule`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/OptimalSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A feasible single-item allocation rule satisfies `IsAllocFeasible` with any payment rule.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open scoped BigOperators in
open MeasureTheory in
variable {I : Type*} in
/-- A feasible single-item allocation rule satisfies `IsAllocFeasible` with any payment rule. -/
theorem BayesianSingleItemAuction.withPayment_isAllocFeasible_of_isSingleItemAllocationRule
    [Fintype I] [DecidableEq I] {x p : (I → ℝ) → I → ℝ}
    (hx : IsSingleItemAllocationRule x) :
    ({ allocationRule := x, paymentRule := p } :
      SingleParameterMechanism I ℝ).IsAllocFeasible := by
  intro b i
  exact ⟨hx.1 b i, hx.le_one b i⟩
