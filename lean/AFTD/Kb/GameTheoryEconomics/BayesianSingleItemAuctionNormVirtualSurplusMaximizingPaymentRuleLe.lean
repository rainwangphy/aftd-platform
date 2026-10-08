import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingPaymentRule
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAllocationRule
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAllocationRuleNonneg
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAllocationRuleLeOne
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingPaymentRuleEq
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
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProductPriorIsProbabilityMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionOpponentProductPriorIsProbabilityMeasure

/-!
# BayesianSingleItemAuction.norm_virtualSurplusMaximizingPaymentRule_le

Topic: mechanism_design   Node: 39cd74a0f278

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.norm_virtualSurplusMaximizingPaymentRule_le`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/OptimalSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The constructed Myerson payment is bounded by twice the absolute report. This uses only the pointwise allocation bounds `0 ≤ x ≤ 1`; it is the boundedness half of the interim-integrability proof route.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open scoped BigOperators in
open MeasureTheory in
variable {I : Type*} in
/-- The constructed Myerson payment is bounded by twice the absolute report. This uses only the pointwise allocation bounds `0 ≤ x ≤ 1`; it is the boundedness half of the interim-integrability proof route. -/
theorem BayesianSingleItemAuction.norm_virtualSurplusMaximizingPaymentRule_le
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ) (i : I) :
    ‖A.virtualSurplusMaximizingPaymentRule b i‖ ≤ 2 * ‖b i‖ := by
  let x : ℝ := A.virtualSurplusMaximizingAllocationRule b i
  have hx_nonneg : 0 ≤ x := by
    simpa [x] using A.virtualSurplusMaximizingAllocationRule_nonneg b i
  have hx_le_one : x ≤ 1 := by
    simpa [x] using A.virtualSurplusMaximizingAllocationRule_le_one b i
  have hterm :
      ‖b i * A.virtualSurplusMaximizingAllocationRule b i‖ ≤ ‖b i‖ := by
    calc
      ‖b i * A.virtualSurplusMaximizingAllocationRule b i‖
          = |b i| * x := by
            simp [x, Real.norm_eq_abs, abs_of_nonneg hx_nonneg]
      _ ≤ |b i| * 1 := mul_le_mul_of_nonneg_left hx_le_one (abs_nonneg (b i))
      _ = ‖b i‖ := by simp [Real.norm_eq_abs]
  have hintegral :
      ‖∫ z in 0..b i, A.virtualSurplusMaximizingAllocationRule (Function.update b i z) i‖
        ≤ ‖b i‖ := by
    have hbound :
        ‖∫ z in 0..b i,
            A.virtualSurplusMaximizingAllocationRule (Function.update b i z) i‖
          ≤ 1 * |b i - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (fun z _hz => by
          have hz_nonneg :
              0 ≤ A.virtualSurplusMaximizingAllocationRule (Function.update b i z) i :=
            A.virtualSurplusMaximizingAllocationRule_nonneg (Function.update b i z) i
          have hz_le_one :
              A.virtualSurplusMaximizingAllocationRule (Function.update b i z) i ≤ 1 :=
            A.virtualSurplusMaximizingAllocationRule_le_one (Function.update b i z) i
          simpa [Real.norm_eq_abs, abs_of_nonneg hz_nonneg] using hz_le_one)
    simpa [Real.norm_eq_abs] using hbound
  calc
    ‖A.virtualSurplusMaximizingPaymentRule b i‖
        = ‖b i * A.virtualSurplusMaximizingAllocationRule b i -
            ∫ z in 0..b i,
              A.virtualSurplusMaximizingAllocationRule (Function.update b i z) i‖ := by
          rw [A.virtualSurplusMaximizingPaymentRule_eq]
    _ ≤ ‖b i * A.virtualSurplusMaximizingAllocationRule b i‖ +
          ‖∫ z in 0..b i,
            A.virtualSurplusMaximizingAllocationRule (Function.update b i z) i‖ :=
          norm_sub_le _ _
    _ ≤ ‖b i‖ + ‖b i‖ := add_le_add hterm hintegral
    _ = 2 * ‖b i‖ := by ring
