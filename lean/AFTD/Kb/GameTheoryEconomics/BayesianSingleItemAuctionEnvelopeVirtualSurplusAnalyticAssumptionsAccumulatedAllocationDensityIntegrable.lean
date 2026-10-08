import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionEnvelopeVirtualSurplusAnalyticAssumptions
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocProb
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionTypeDensity
import AFTD.Kb.GameTheoryEconomics.ContinuousTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionEnvelopeVirtualSurplusAnalyticAssumptionsInterimAllocationIntervalIntegrableOnSupport
import AFTD.Kb.GameTheoryEconomics.TypeCDF
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
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProductPriorIsProbabilityMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionOpponentProductPriorIsProbabilityMeasure

/-!
# BayesianSingleItemAuction.EnvelopeVirtualSurplusAnalyticAssumptions.accumulatedAllocation_density_integrable

Topic: mechanism_design   Node: 90deff725123

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.EnvelopeVirtualSurplusAnalyticAssumptions.accumulatedAllocation_density_integrable`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/OptimalSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

BayesianSingleItemAuction.EnvelopeVirtualSurplusAnalyticAssumptions.accumulatedAllocation_density_integrable
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open scoped BigOperators in
open MeasureTheory in
variable {I : Type*} in
theorem BayesianSingleItemAuction.EnvelopeVirtualSurplusAnalyticAssumptions.accumulatedAllocation_density_integrable
    {A B : BayesianSingleItemAuction I}
    (h : A.EnvelopeVirtualSurplusAnalyticAssumptions B) (i : I) :
    IntervalIntegrable
      (fun v => (∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v)
      volume 0 (A.typeData.omega i) := by
  have hQ := h.interim_allocation_intervalIntegrableOnSupport i
  have hAC := h.cdf_absolutelyContinuous i
  have h0mem : (0 : ℝ) ∈ Set.uIcc 0 (A.typeData.omega i) := by
    rw [Set.uIcc_of_le (A.typeData.cdf i).omega_nonneg]
    exact ⟨le_rfl, (A.typeData.cdf i).omega_nonneg⟩
  have hG : AbsolutelyContinuousOnInterval
      (fun v => ∫ z in 0..v, B.interimAllocProb i z) 0 (A.typeData.omega i) :=
    hQ.absolutelyContinuousOnInterval_intervalIntegral h0mem
  have hderiv_int :
      IntervalIntegrable
        (fun v => (∫ z in 0..v, B.interimAllocProb i z) * deriv (A.typeData.cdf i).cdf v)
        volume 0 (A.typeData.omega i) :=
    hAC.intervalIntegrable_deriv.continuousOn_mul hG.continuousOn
  simpa [typeDensity] using hderiv_int
