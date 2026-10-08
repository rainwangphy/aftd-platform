import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.OpponentTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocationIntegrand
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimPaymentIntegrand
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasIntegrableInterimObjects
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasIntegrableInterimObjectsOfAestronglyMeasurableOfBound
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAuctionOpponentPrior
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfile
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsAllocFeasible
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionRespectsSingleItemCapacity
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAuctionIsFeasible
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismWithMyersonPayment
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAllocationRule
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingMechanism
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAuctionToSingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingMechanismEqWithMyersonPayment
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAuctionInterimPaymentIntegrandBound
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
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAuctionTypeData
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAuctionToDirectBayesianMechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingPaymentRuleEq
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProductPriorIsProbabilityMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionOpponentProductPriorIsProbabilityMeasure

/-!
# BayesianSingleItemAuction.virtualSurplusMaximizingAuction_hasIntegrableInterimObjects_of_aestronglyMeasurable

Topic: mechanism_design   Node: 58c0f59f625a

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.virtualSurplusMaximizingAuction_hasIntegrableInterimObjects_of_aestronglyMeasurable`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/OptimalSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Once the constructed allocation and payment integrands are measurable, boundedness gives interim integrability for the constructed auction.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open scoped BigOperators in
open MeasureTheory in
variable {I : Type*} in
/-- Once the constructed allocation and payment integrands are measurable, boundedness gives interim integrability for the constructed auction. -/
theorem BayesianSingleItemAuction.virtualSurplusMaximizingAuction_hasIntegrableInterimObjects_of_aestronglyMeasurable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I)
    (halloc_meas :
      ∀ i z_i,
        AEStronglyMeasurable
          (fun t =>
            A.virtualSurplusMaximizingAuction.interimAllocationIntegrand i z_i t)
          (A.opponentPrior i))
    (hpay_meas :
      ∀ i z_i,
        AEStronglyMeasurable
          (fun t =>
            A.virtualSurplusMaximizingAuction.interimPaymentIntegrand i z_i t)
          (A.opponentPrior i)) :
    A.virtualSurplusMaximizingAuction.HasIntegrableInterimObjects :=
  A.virtualSurplusMaximizingAuction
    |>.hasIntegrableInterimObjects_of_aestronglyMeasurable_of_bound
      (by simpa [virtualSurplusMaximizingAuction_opponentPrior] using halloc_meas)
      (by simpa [virtualSurplusMaximizingAuction_opponentPrior] using hpay_meas)
      (by
        intro i z_i
        refine ⟨1, Filter.Eventually.of_forall ?_⟩
        intro t
        have hx :=
          A.virtualSurplusMaximizingAuction_isFeasible.1 (reportProfile i z_i t) i
        have hnonneg :
            0 ≤
              A.virtualSurplusMaximizingAuction.interimAllocationIntegrand i z_i t := by
          simpa [interimAllocationIntegrand] using hx.1
        have hle :
            A.virtualSurplusMaximizingAuction.interimAllocationIntegrand i z_i t ≤ 1 := by
          simpa [interimAllocationIntegrand] using hx.2
        rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
        exact hle)
      (by
        intro i z_i
        exact ⟨2 * ‖z_i‖,
          A.virtualSurplusMaximizingAuction_interimPaymentIntegrand_bound i z_i⟩)
