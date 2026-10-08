import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIsFeasible
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasIntegrableInterimAllocation
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocProb
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocProbNonnegOfIsFeasible
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocProbLeOneOfIsFeasible
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
# BayesianSingleItemAuction.interimAllocProb_mem_Icc_of_isFeasible

Topic: mechanism_design   Node: 88a5ba194698

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.interimAllocProb_mem_Icc_of_isFeasible`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Feasible interim allocation probabilities lie in `[0, 1]`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
/-- Feasible interim allocation probabilities lie in `[0, 1]`. -/
theorem BayesianSingleItemAuction.interimAllocProb_mem_Icc_of_isFeasible
    [Fintype I] (A : BayesianSingleItemAuction I)
    (hfeas : A.IsFeasible) (hint : A.HasIntegrableInterimAllocation)
    (i : I) (z_i : ℝ) :
    A.interimAllocProb i z_i ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨A.interimAllocProb_nonneg_of_isFeasible hfeas i z_i,
    A.interimAllocProb_le_one_of_isFeasible hfeas hint i z_i⟩
