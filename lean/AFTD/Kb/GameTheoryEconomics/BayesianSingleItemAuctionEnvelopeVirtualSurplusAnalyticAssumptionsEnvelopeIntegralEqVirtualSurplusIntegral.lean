import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionEnvelopeVirtualSurplusAnalyticAssumptions
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocProb
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionTypeDensity
import AFTD.Kb.GameTheoryEconomics.ContinuousTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualValue
import AFTD.Kb.GameTheoryEconomics.TypeCDF
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionEnvelopeVirtualSurplusAnalyticAssumptionsSurvivalIntegralEqAccumulatedDensity
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionEnvelopeVirtualSurplusAnalyticAssumptionsEnvelopeIntegrandEqOnSupport
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionEnvelopeVirtualSurplusAnalyticAssumptionsAccumulatedAllocationDensityIntegrable
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
# BayesianSingleItemAuction.EnvelopeVirtualSurplusAnalyticAssumptions.envelopeIntegral_eq_virtualSurplusIntegral

Topic: mechanism_design   Node: d4adca4e20de

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.EnvelopeVirtualSurplusAnalyticAssumptions.envelopeIntegral_eq_virtualSurplusIntegral`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/OptimalSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

BayesianSingleItemAuction.EnvelopeVirtualSurplusAnalyticAssumptions.envelopeIntegral_eq_virtualSurplusIntegral
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open scoped BigOperators in
open MeasureTheory in
variable {I : Type*} in
theorem BayesianSingleItemAuction.EnvelopeVirtualSurplusAnalyticAssumptions.envelopeIntegral_eq_virtualSurplusIntegral
    {A B : BayesianSingleItemAuction I}
    (h : A.EnvelopeVirtualSurplusAnalyticAssumptions B) (i : I) :
    (∫ v in 0..A.typeData.omega i,
      (B.interimAllocProb i v * v -
        ∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v) =
      ∫ v in 0..A.typeData.omega i,
        B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v := by
  have hsurv := h.survivalIntegral_eq_accumulatedDensity i
  have hvirt_int := h.interim_virtual_surplus_integrable i
  have hcongr :
      (∫ v in 0..A.typeData.omega i,
        (B.interimAllocProb i v * v -
          ∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v) =
        ∫ v in 0..A.typeData.omega i,
          B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v +
            B.interimAllocProb i v * (1 - (A.typeData.cdf i).cdf v) -
              (∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with v hv
    exact h.envelopeIntegrand_eq_onSupport i hv
  have hderiv_int := h.accumulatedAllocation_density_integrable i
  calc
    (∫ v in 0..A.typeData.omega i,
        (B.interimAllocProb i v * v -
          ∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v)
        = ∫ v in 0..A.typeData.omega i,
            B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v +
              B.interimAllocProb i v * (1 - (A.typeData.cdf i).cdf v) -
                (∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v := hcongr
    _ = (∫ v in 0..A.typeData.omega i,
            B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v) -
          (-(∫ v in 0..A.typeData.omega i,
            B.interimAllocProb i v * (1 - (A.typeData.cdf i).cdf v))) -
            ∫ v in 0..A.typeData.omega i,
              (∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v := by
          rw [intervalIntegral.integral_sub
            (hvirt_int.add (h.interim_allocation_survival_integrable i)) hderiv_int,
            intervalIntegral.integral_add hvirt_int (h.interim_allocation_survival_integrable i)]
          ring
    _ = ∫ v in 0..A.typeData.omega i,
          B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v := by
          rw [hsurv]
          ring
