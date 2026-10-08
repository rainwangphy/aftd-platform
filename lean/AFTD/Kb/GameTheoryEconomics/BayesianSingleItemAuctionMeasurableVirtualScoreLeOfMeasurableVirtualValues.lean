import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualValue
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualScore
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
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProductPriorIsProbabilityMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionOpponentProductPriorIsProbabilityMeasure

/-!
# BayesianSingleItemAuction.measurable_virtualScore_le_of_measurable_virtualValues

Topic: mechanism_design   Node: 5d5edf930083

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.measurable_virtualScore_le_of_measurable_virtualValues`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/OptimalSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

BayesianSingleItemAuction.measurable_virtualScore_le_of_measurable_virtualValues
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open scoped BigOperators in
open MeasureTheory in
variable {I : Type*} in
lemma BayesianSingleItemAuction.measurable_virtualScore_le_of_measurable_virtualValues
    [Fintype I] [LinearOrder I] {X : Type*} [MeasurableSpace X]
    (A : BayesianSingleItemAuction I) (b : X → I → ℝ)
    (hb : ∀ j, Measurable fun t => A.virtualValue j (b t j)) (i j : I) :
    MeasurableSet {t | A.virtualScore (b t) j ≤ A.virtualScore (b t) i} := by
  have hset :
      {t | A.virtualScore (b t) j ≤ A.virtualScore (b t) i} =
        {t | A.virtualValue j (b t j) < A.virtualValue i (b t i) ∨
          A.virtualValue j (b t j) = A.virtualValue i (b t i) ∧ j ≤ i} := by
    ext t
    simp [virtualScore, Prod.Lex.toLex_le_toLex]
  rw [hset]
  by_cases hji : j ≤ i
  · have hset' :
        {t | A.virtualValue j (b t j) < A.virtualValue i (b t i) ∨
          A.virtualValue j (b t j) = A.virtualValue i (b t i) ∧ j ≤ i} =
          {t | A.virtualValue j (b t j) < A.virtualValue i (b t i)} ∪
            {t | A.virtualValue j (b t j) = A.virtualValue i (b t i)} := by
      ext t
      simp [hji]
    rw [hset']
    exact (measurableSet_lt (hb j) (hb i)).union
      (measurableSet_eq_fun (hb j) (hb i))
  · have hset' :
        {t | A.virtualValue j (b t j) < A.virtualValue i (b t i) ∨
          A.virtualValue j (b t j) = A.virtualValue i (b t i) ∧ j ≤ i} =
          {t | A.virtualValue j (b t j) < A.virtualValue i (b t i)} := by
      ext t
      simp [hji]
    rw [hset']
    exact measurableSet_lt (hb j) (hb i)
