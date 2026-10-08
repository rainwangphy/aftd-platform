import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionTypeDensity
import AFTD.Kb.GameTheoryEconomics.ContinuousTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimExpectedPayment
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocProb
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasInterimPaymentEnvelopeUpperBound
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
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAuctionHasSameSellingEnvironment
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProductPriorIsProbabilityMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionOpponentProductPriorIsProbabilityMeasure

/-!
# BayesianSingleItemAuction.hasInterimPaymentEnvelopeUpperBound_of_pointwise

Topic: mechanism_design   Node: ad2282e29bb9

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.hasInterimPaymentEnvelopeUpperBound_of_pointwise`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/OptimalSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

BayesianSingleItemAuction.hasInterimPaymentEnvelopeUpperBound_of_pointwise
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open scoped BigOperators in
open MeasureTheory in
variable {I : Type*} in
theorem BayesianSingleItemAuction.hasInterimPaymentEnvelopeUpperBound_of_pointwise
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
    (hpoint :
      ∀ (i : I) (v : ℝ),
        0 ≤ v →
          v ≤ A.typeData.omega i →
            B.interimExpectedPayment i v ≤
              B.interimAllocProb i v * v -
                ∫ z in 0..v, B.interimAllocProb i z) :
    A.HasInterimPaymentEnvelopeUpperBound B := by
  intro i
  have hae :
      (fun v : ℝ => B.interimExpectedPayment i v * A.typeDensity i v)
        ≤ᵐ[volume.restrict (Set.Ioc 0 (A.typeData.omega i))]
      (fun v : ℝ =>
        (B.interimAllocProb i v * v -
          ∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hdens_ae i] with v hv hdens_v
    exact mul_le_mul_of_nonneg_right (hpoint i v hv.1.le hv.2) hdens_v
  rw [intervalIntegral.integral_of_le (A.typeData.cdf i).omega_nonneg,
    intervalIntegral.integral_of_le (A.typeData.cdf i).omega_nonneg]
  exact setIntegral_mono_ae_restrict (hint_pay i).1 (hint_env i).1 hae
