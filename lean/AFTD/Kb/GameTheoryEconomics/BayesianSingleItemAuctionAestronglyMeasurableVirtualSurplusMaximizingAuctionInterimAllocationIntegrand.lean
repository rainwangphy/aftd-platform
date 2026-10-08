import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.OpponentTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualValue
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocationIntegrand
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAllocationRule
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionMeasurableVirtualSurplusMaximizingAllocationRuleCompOfMeasurableVirtualValues
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingMechanism
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
# BayesianSingleItemAuction.aestronglyMeasurable_virtualSurplusMaximizingAuction_interimAllocationIntegrand

Topic: mechanism_design   Node: 84f91c0d9bf9

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.aestronglyMeasurable_virtualSurplusMaximizingAuction_interimAllocationIntegrand`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/OptimalSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

BayesianSingleItemAuction.aestronglyMeasurable_virtualSurplusMaximizingAuction_interimAllocationIntegrand
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open scoped BigOperators in
open MeasureTheory in
variable {I : Type*} in
lemma BayesianSingleItemAuction.aestronglyMeasurable_virtualSurplusMaximizingAuction_interimAllocationIntegrand
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I)
    (hmeas :
      ∀ i z_i j,
        Measurable fun t : OpponentTypeProfile I i =>
          A.virtualValue j (reportProfile i z_i t j)) :
    ∀ i z_i,
      AEStronglyMeasurable
        (fun t =>
          A.virtualSurplusMaximizingAuction.interimAllocationIntegrand i z_i t)
        (A.opponentPrior i) := by
  intro i z_i
  have hmeas_alloc :
      Measurable fun t : OpponentTypeProfile I i =>
        A.virtualSurplusMaximizingAllocationRule (reportProfile i z_i t) i :=
    A.measurable_virtualSurplusMaximizingAllocationRule_comp_of_measurable_virtualValues
      (fun t => reportProfile i z_i t) (hmeas i z_i) i
  simpa [interimAllocationIntegrand, virtualSurplusMaximizingAuction,
    virtualSurplusMaximizingMechanism] using hmeas_alloc.aestronglyMeasurable
