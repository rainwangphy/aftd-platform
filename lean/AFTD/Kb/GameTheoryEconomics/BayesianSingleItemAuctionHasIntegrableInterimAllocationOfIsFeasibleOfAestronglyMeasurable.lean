import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIsFeasible
import AFTD.Kb.GameTheoryEconomics.OpponentTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocationIntegrand
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasIntegrableInterimAllocation
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasIntegrableInterimAllocationOfAestronglyMeasurableOfBound
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfile
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsAllocFeasible
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionRespectsSingleItemCapacity
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
# BayesianSingleItemAuction.hasIntegrableInterimAllocation_of_isFeasible_of_aestronglyMeasurable

Topic: mechanism_design   Node: 4416253a5c88

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.hasIntegrableInterimAllocation_of_isFeasible_of_aestronglyMeasurable`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Feasibility and a.e. strong measurability imply allocation integrability.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
/-- Feasibility and a.e. strong measurability imply allocation integrability. -/
theorem BayesianSingleItemAuction.hasIntegrableInterimAllocation_of_isFeasible_of_aestronglyMeasurable
    [Fintype I] (A : BayesianSingleItemAuction I)
    (hfeas : A.IsFeasible)
    (hmeas :
      ∀ i z_i,
        AEStronglyMeasurable
          (fun t => A.interimAllocationIntegrand i z_i t)
          (A.opponentPrior i)) :
    A.HasIntegrableInterimAllocation := by
  refine A.hasIntegrableInterimAllocation_of_aestronglyMeasurable_of_bound hmeas ?_
  intro i z_i
  refine ⟨1, Filter.Eventually.of_forall ?_⟩
  intro t
  have hx := hfeas.1 (reportProfile i z_i t) i
  simpa [interimAllocationIntegrand, Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
