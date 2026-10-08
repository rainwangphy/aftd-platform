import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionEnvelopeVirtualSurplusAnalyticAssumptions
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocProb
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionTypeDensity
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualValue
import AFTD.Kb.GameTheoryEconomics.TypeCDF
import AFTD.Kb.GameTheoryEconomics.ContinuousTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasPositiveDensityOnSupportNonzeroOnSupport
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
# BayesianSingleItemAuction.EnvelopeVirtualSurplusAnalyticAssumptions.envelopeIntegrand_eq_onSupport

Topic: mechanism_design   Node: e00f99bad542

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.EnvelopeVirtualSurplusAnalyticAssumptions.envelopeIntegrand_eq_onSupport`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/OptimalSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

BayesianSingleItemAuction.EnvelopeVirtualSurplusAnalyticAssumptions.envelopeIntegrand_eq_onSupport
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open scoped BigOperators in
open MeasureTheory in
variable {I : Type*} in
theorem BayesianSingleItemAuction.EnvelopeVirtualSurplusAnalyticAssumptions.envelopeIntegrand_eq_onSupport
    {A B : BayesianSingleItemAuction I}
    (h : A.EnvelopeVirtualSurplusAnalyticAssumptions B) (i : I) :
    Set.EqOn
      (fun v =>
        (B.interimAllocProb i v * v -
          ∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v)
      (fun v =>
        B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v +
          B.interimAllocProb i v * (1 - (A.typeData.cdf i).cdf v) -
            (∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v)
      (Set.uIoc 0 (A.typeData.omega i)) := by
  intro v hv
  have hv' : v ∈ Set.Ioc 0 (A.typeData.omega i) := by
    simpa [Set.uIoc_of_le (A.typeData.cdf i).omega_nonneg] using hv
  have h0 : 0 < v := hv'.1
  have homega : v ≤ A.typeData.omega i := hv'.2
  have homega_lt_or_eq : v < A.typeData.omega i ∨ v = A.typeData.omega i :=
    lt_or_eq_of_le homega
  rcases homega_lt_or_eq with homega_lt | rfl
  · have hdens_ne :
        A.typeDensity i v ≠ 0 :=
      h.positive_density_on_support.nonzero_on_support A h0 homega_lt
    simp [virtualValue, mul_sub, sub_mul, mul_assoc, div_eq_mul_inv, hdens_ne]
  · have hFω : (A.typeData.cdf i).cdf (A.typeData.omega i) = 1 :=
      (A.typeData.cdf i).cdf_upper
    have hsurv_zero : 1 - (A.typeData.cdf i).cdf (A.typeData.omega i) = 0 := by
      rw [hFω]
      ring
    simp [virtualValue, hsurv_zero, sub_mul]
