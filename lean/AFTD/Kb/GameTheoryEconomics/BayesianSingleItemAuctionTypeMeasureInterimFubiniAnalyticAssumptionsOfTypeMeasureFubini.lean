import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionTypeDensity
import AFTD.Kb.GameTheoryEconomics.ContinuousTypeProfile
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualValue
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionTypeMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimExpectedPayment
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocProb
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionTypeMeasureInterimFubiniAnalyticAssumptions
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionTypeDensityEnnrealOfRealAemeasurable
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
# BayesianSingleItemAuction.typeMeasureInterimFubiniAnalyticAssumptions_of_typeMeasure_fubini

Topic: mechanism_design   Node: c67cb101c4e1

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.typeMeasureInterimFubiniAnalyticAssumptions_of_typeMeasure_fubini`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/OptimalSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

BayesianSingleItemAuction.typeMeasureInterimFubiniAnalyticAssumptions_of_typeMeasure_fubini
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open scoped BigOperators in
open MeasureTheory in
variable {I : Type*} in
theorem BayesianSingleItemAuction.typeMeasureInterimFubiniAnalyticAssumptions_of_typeMeasure_fubini
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (hdens_ae :
      ∀ i : I,
        ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 (A.typeData.omega i))),
          0 ≤ A.typeDensity i v)
    (hpay_int : ∀ i : I, Integrable (fun t => B.paymentRule t i) A.prior)
    (hvs_int :
      ∀ i : I, Integrable (fun t => B.allocationRule t i * A.virtualValue i (t i))
        A.prior)
    (hpay_fubini :
      ∀ i : I,
        (∫ t, B.paymentRule t i ∂A.prior) =
          ∫ v, B.interimExpectedPayment i v ∂A.typeMeasure i)
    (hvs_fubini :
      ∀ i : I,
        (∫ t, B.allocationRule t i * A.virtualValue i (t i) ∂A.prior) =
          ∫ v, B.interimAllocProb i v * A.virtualValue i v ∂A.typeMeasure i) :
    A.TypeMeasureInterimFubiniAnalyticAssumptions B where
  payment_integrable := hpay_int
  virtual_surplus_integrable := hvs_int
  type_density_measurable := fun i => A.typeDensity_ennreal_ofReal_aemeasurable i
  type_density_nonnegative_ae := hdens_ae
  payment_typeMeasure_fubini := hpay_fubini
  virtual_surplus_typeMeasure_fubini := hvs_fubini
