import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasIntegrableInterimAllocation
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasIntegrableInterimPayment
import AFTD.Kb.GameTheoryEconomics.OpponentTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimQuasiLinearUtilityIntegrand
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimQuasiLinearUtility
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocProb
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimExpectedPayment
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocationIntegrand
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimPaymentIntegrand
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfileSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfileOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionUpdateReportProfileSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileSplitMeasurableEquivApplyFst
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileSplitMeasurableEquivApplySnd
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileSplitMeasurableEquivSymmApply
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionExpectedSellerRevenueInEnvironmentSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProductPriorIsProbabilityMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionOpponentProductPriorIsProbabilityMeasure

/-!
# BayesianSingleItemAuction.integral_interimQuasiLinearUtilityIntegrand_eq

Topic: mechanism_design   Node: 9284649603b7

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.integral_interimQuasiLinearUtilityIntegrand_eq`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The utility integrand integrates to interim utility.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
/-- The utility integrand integrates to interim utility. -/
theorem BayesianSingleItemAuction.integral_interimQuasiLinearUtilityIntegrand_eq
    (A : BayesianSingleItemAuction I)
    (hQ : A.HasIntegrableInterimAllocation) (hM : A.HasIntegrableInterimPayment)
    (i : I) (t_i z_i : ℝ) :
    (∫ t, A.interimQuasiLinearUtilityIntegrand i t_i z_i t ∂A.opponentPrior i) =
      A.interimQuasiLinearUtility i t_i z_i := by
  calc
    (∫ t, A.interimQuasiLinearUtilityIntegrand i t_i z_i t ∂A.opponentPrior i)
        = (∫ t, t_i * A.interimAllocationIntegrand i z_i t -
            A.interimPaymentIntegrand i z_i t ∂A.opponentPrior i) := by
          rfl
    _ = (∫ t, t_i * A.interimAllocationIntegrand i z_i t ∂A.opponentPrior i) -
          ∫ t, A.interimPaymentIntegrand i z_i t ∂A.opponentPrior i := by
          exact integral_sub ((hQ i z_i).const_mul t_i) (hM i z_i)
    _ = t_i * A.interimAllocProb i z_i - A.interimExpectedPayment i z_i := by
          rw [integral_const_mul]
          rfl
    _ = A.interimQuasiLinearUtility i t_i z_i := by
          rw [interimQuasiLinearUtility]
          ring
