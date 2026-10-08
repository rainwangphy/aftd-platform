import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionTypeDensity
import AFTD.Kb.GameTheoryEconomics.ContinuousTypeProfile
import AFTD.Kb.GameTheoryEconomics.OpponentTypeProfile
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualValue
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionTypeMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocProb
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
import AFTD.Kb.GameTheoryEconomics.TypeCDF
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimExpectation
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
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProductPriorIsProbabilityMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionOpponentProductPriorIsProbabilityMeasure

/-!
# BayesianSingleItemAuction.intervalIntegrable_interimAllocProb_mul_virtualValue_mul_typeDensity_of_profileSplit_integrable

Topic: mechanism_design   Node: ab0a373015cf

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.intervalIntegrable_interimAllocProb_mul_virtualValue_mul_typeDensity_of_profileSplit_integrable`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/OptimalSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Product-side virtual-surplus integrability gives interval integrability of the density-weighted interim virtual surplus.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open scoped BigOperators in
open MeasureTheory in
variable {I : Type*} in
/-- Product-side virtual-surplus integrability gives interval integrability of the density-weighted interim virtual surplus. -/
theorem BayesianSingleItemAuction.intervalIntegrable_interimAllocProb_mul_virtualValue_mul_typeDensity_of_profileSplit_integrable
    {A B : BayesianSingleItemAuction I} (i : I)
    (hmeas :
      AEMeasurable
        (fun v => ENNReal.ofReal (A.typeDensity i v))
        (volume.restrict (Set.Ioc 0 (A.typeData.omega i))))
    (hnonneg :
      ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 (A.typeData.omega i))),
        0 ≤ A.typeDensity i v)
    (hvs :
      Integrable
        (fun p : ℝ × OpponentTypeProfile I i =>
          B.allocationRule (reportProfile i p.1 p.2) i * A.virtualValue i p.1)
        ((A.typeMeasure i).prod (B.opponentPrior i))) :
    IntervalIntegrable
      (fun v => B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v)
      volume 0 (A.typeData.omega i) := by
  let s := Set.Ioc (0 : ℝ) (A.typeData.omega i)
  have hinner :
      Integrable
        (fun v : ℝ =>
          ∫ t, B.allocationRule (reportProfile i v t) i * A.virtualValue i v
            ∂B.opponentPrior i)
        (A.typeMeasure i) := by
    simpa using hvs.integral_prod_left
  have htop :
      ∀ᵐ v ∂(volume.restrict s),
        ENNReal.ofReal (A.typeDensity i v) < (⊤ : ENNReal) :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hinner' :
      Integrable
        (fun v : ℝ =>
          ∫ t, B.allocationRule (reportProfile i v t) i * A.virtualValue i v
            ∂B.opponentPrior i)
        ((volume.restrict s).withDensity fun v => ENNReal.ofReal (A.typeDensity i v)) := by
    simpa [typeMeasure, s] using hinner
  have hsmul :
      Integrable
        (fun v : ℝ =>
          (ENNReal.ofReal (A.typeDensity i v)).toReal •
            (∫ t, B.allocationRule (reportProfile i v t) i * A.virtualValue i v
              ∂B.opponentPrior i))
        (volume.restrict s) :=
    (integrable_withDensity_iff_integrable_smul₀' hmeas htop).mp hinner'
  have hmul :
      Integrable
        (fun v : ℝ =>
          (∫ t, B.allocationRule (reportProfile i v t) i * A.virtualValue i v
            ∂B.opponentPrior i) * A.typeDensity i v)
        (volume.restrict s) := by
    refine hsmul.congr ?_
    filter_upwards [hnonneg] with v hv
    rw [ENNReal.toReal_ofReal hv]
    simp [smul_eq_mul, mul_comm]
  have hcongr :
      (fun v : ℝ =>
          (∫ t, B.allocationRule (reportProfile i v t) i * A.virtualValue i v
            ∂B.opponentPrior i) * A.typeDensity i v) =
        fun v : ℝ =>
          B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v := by
    funext v
    simp [interimAllocProb, interimExpectation, integral_mul_const]
  have hint :
      Integrable
        (fun v => B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v)
        (volume.restrict s) := by
    simpa [hcongr, s] using hmul
  rw [intervalIntegrable_iff, Set.uIoc_of_le (A.typeData.cdf i).omega_nonneg]
  simpa [IntegrableOn, s] using hint
