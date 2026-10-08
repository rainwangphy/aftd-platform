import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.OpponentTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocationIntegrand
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimPaymentIntegrand
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasIntegrableInterimObjects
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasIntegrableInterimAllocation
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasIntegrableInterimPayment
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasIntegrableInterimAllocationOfAestronglyMeasurableOfBound
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasIntegrableInterimPaymentOfAestronglyMeasurableOfBound
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfileSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfileOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionUpdateReportProfileSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileSplitMeasurableEquivApplyFst
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileSplitMeasurableEquivApplySnd
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileSplitMeasurableEquivSymmApply
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProductPriorIsProbabilityMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionOpponentProductPriorIsProbabilityMeasure

/-!
# BayesianSingleItemAuction.hasIntegrableInterimObjects_of_aestronglyMeasurable_of_bound

Topic: mechanism_design   Node: 0abc663ab1d6

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.hasIntegrableInterimObjects_of_aestronglyMeasurable_of_bound`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A.e. strong measurability and bounds imply interim integrability.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
/-- A.e. strong measurability and bounds imply interim integrability. -/
theorem BayesianSingleItemAuction.hasIntegrableInterimObjects_of_aestronglyMeasurable_of_bound
    (A : BayesianSingleItemAuction I)
    (halloc_meas :
      ∀ i z_i,
        AEStronglyMeasurable
          (fun t => A.interimAllocationIntegrand i z_i t)
          (A.opponentPrior i))
    (hpay_meas :
      ∀ i z_i,
        AEStronglyMeasurable
          (fun t => A.interimPaymentIntegrand i z_i t)
          (A.opponentPrior i))
    (halloc_bound :
      ∀ i z_i,
        ∃ C : ℝ,
          ∀ᵐ t ∂A.opponentPrior i, ‖A.interimAllocationIntegrand i z_i t‖ ≤ C)
    (hpay_bound :
      ∀ i z_i,
        ∃ C : ℝ,
          ∀ᵐ t ∂A.opponentPrior i, ‖A.interimPaymentIntegrand i z_i t‖ ≤ C) :
    A.HasIntegrableInterimObjects :=
  ⟨A.hasIntegrableInterimAllocation_of_aestronglyMeasurable_of_bound
      halloc_meas halloc_bound,
    A.hasIntegrableInterimPayment_of_aestronglyMeasurable_of_bound
      hpay_meas hpay_bound⟩
