import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIsFeasible
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasIntegrableInterimAllocation
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocProb
import AFTD.Kb.GameTheoryEconomics.OpponentTypeProfile
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
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
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProductPriorIsProbabilityMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionOpponentProductPriorIsProbabilityMeasure

/-!
# BayesianSingleItemAuction.interimAllocProb_le_one_of_isFeasible

Topic: mechanism_design   Node: 9086d00f377c

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.interimAllocProb_le_one_of_isFeasible`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Feasible auctions have interim allocation probabilities at most `1`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
/-- Feasible auctions have interim allocation probabilities at most `1`. -/
theorem BayesianSingleItemAuction.interimAllocProb_le_one_of_isFeasible
    [Fintype I] (A : BayesianSingleItemAuction I)
    (hfeas : A.IsFeasible) (hint : A.HasIntegrableInterimAllocation)
    (i : I) (z_i : ℝ) :
    A.interimAllocProb i z_i ≤ 1 := by
  have hle :
      A.interimAllocProb i z_i ≤
        ∫ _ : OpponentTypeProfile I i, (1 : ℝ) ∂A.opponentPrior i := by
    exact integral_mono (hint i z_i) (integrable_const (1 : ℝ)) fun t =>
      (hfeas.1 (reportProfile i z_i t) i).2
  simpa using hle
