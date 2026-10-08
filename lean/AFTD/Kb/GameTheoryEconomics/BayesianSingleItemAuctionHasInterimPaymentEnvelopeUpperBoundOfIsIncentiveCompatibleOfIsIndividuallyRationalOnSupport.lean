import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionTypeDensity
import AFTD.Kb.GameTheoryEconomics.ContinuousTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimExpectedPayment
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocProb
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIsIncentiveCompatible
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIsIndividuallyRationalOnSupport
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasInterimPaymentEnvelopeUpperBound
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasInterimPaymentEnvelopeUpperBoundOfPointwise
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimExpectedPaymentLeAllocMulSubIntegralOfIsIncentiveCompatibleOfIsIndividuallyRationalOnSupport
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
# BayesianSingleItemAuction.hasInterimPaymentEnvelopeUpperBound_of_isIncentiveCompatible_of_isIndividuallyRationalOnSupport

Topic: mechanism_design   Node: c5f02d2d1ea8

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.hasInterimPaymentEnvelopeUpperBound_of_isIncentiveCompatible_of_isIndividuallyRationalOnSupport`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/OptimalSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

BayesianSingleItemAuction.hasInterimPaymentEnvelopeUpperBound_of_isIncentiveCompatible_of_isIndividuallyRationalOnSupport
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open scoped BigOperators in
open MeasureTheory in
variable {I : Type*} in
theorem BayesianSingleItemAuction.hasInterimPaymentEnvelopeUpperBound_of_isIncentiveCompatible_of_isIndividuallyRationalOnSupport
    [Fintype I] (A B : BayesianSingleItemAuction I)
    (hdens_ae :
      ∀ i : I,
        ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 (A.typeData.omega i))),
          0 ≤ A.typeDensity i v)
    (hint_pay :
      ∀ i : I,
        IntervalIntegrable
          (fun v => B.interimExpectedPayment i v * A.typeDensity i v)
          volume 0 (A.typeData.omega i))
    (hint_env :
      ∀ i : I,
        IntervalIntegrable
          (fun v =>
            (B.interimAllocProb i v * v -
              ∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v)
          volume 0 (A.typeData.omega i))
    (hIC : B.IsIncentiveCompatible)
    (hIR : B.IsIndividuallyRationalOnSupport) :
    A.HasInterimPaymentEnvelopeUpperBound B :=
  A.hasInterimPaymentEnvelopeUpperBound_of_pointwise B hdens_ae hint_pay hint_env
    (fun i v _h0 _homega =>
      BayesianSingleItemAuction.interimExpectedPayment_le_alloc_mul_sub_integral_of_isIncentiveCompatible_of_isIndividuallyRationalOnSupport
        B hIC hIR i v)
