import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionRegularMyersonICIRAnalyticAssumptions
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIsFeasible
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIsIncentiveCompatible
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIsIndividuallyRationalOnSupport
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocProb
import AFTD.Kb.GameTheoryEconomics.TypeCDF
import AFTD.Kb.GameTheoryEconomics.ContinuousTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasIntervalIntegrableInterimAllocationOfIsIncentiveCompatible
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionEnvelopeVirtualSurplusEnvironmentAssumptions
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
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingMechanismEqWithMyersonPayment
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingPaymentRuleEq
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAuctionHasSameSellingEnvironment
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProductPriorIsProbabilityMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionOpponentProductPriorIsProbabilityMeasure

/-!
# BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.candidate_allocation_survival_integrable

Topic: mechanism_design   Node: 634cdf541c61

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.candidate_allocation_survival_integrable`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/OptimalSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.candidate_allocation_survival_integrable
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open scoped BigOperators in
open MeasureTheory in
variable {I : Type*} in
theorem BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.candidate_allocation_survival_integrable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (B : BayesianSingleItemAuction I)
    (_hfeas : B.IsFeasible)
    (hIC : B.IsIncentiveCompatible)
    (_hIR : B.IsIndividuallyRationalOnSupport) :
    ∀ i : I,
      IntervalIntegrable
        (fun v => B.interimAllocProb i v * (1 - (A.typeData.cdf i).cdf v))
        volume 0 (A.typeData.omega i) := by
  intro i
  exact (B.hasIntervalIntegrableInterimAllocation_of_isIncentiveCompatible
    hIC i 0 (A.typeData.omega i)).mul_continuousOn
      (continuousOn_const.sub (h.envelope_environment.cdf_absolutelyContinuous i).continuousOn)
