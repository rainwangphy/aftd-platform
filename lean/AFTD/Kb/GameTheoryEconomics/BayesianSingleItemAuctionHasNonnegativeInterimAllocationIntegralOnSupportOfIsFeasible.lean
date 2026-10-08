import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIsFeasible
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasNonnegativeInterimAllocationIntegralOnSupport
import AFTD.Kb.GameTheoryEconomics.ContinuousTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocProb
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocProbNonnegOfIsFeasible
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
import AFTD.Kb.Tcs.Support

/-!
# BayesianSingleItemAuction.hasNonnegativeInterimAllocationIntegralOnSupport_of_isFeasible

Topic: mechanism_design   Node: c872f8ab54e0

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.hasNonnegativeInterimAllocationIntegralOnSupport_of_isFeasible`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Feasibility gives nonnegative envelope increments on the support.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
/-- Feasibility gives nonnegative envelope increments on the support. -/
theorem BayesianSingleItemAuction.hasNonnegativeInterimAllocationIntegralOnSupport_of_isFeasible
    [Fintype I] (A : BayesianSingleItemAuction I)
    (hfeas : A.IsFeasible) :
    A.HasNonnegativeInterimAllocationIntegralOnSupport := by
  intro i v_i hv_nonneg _hv_le
  exact intervalIntegral.integral_nonneg hv_nonneg fun z _hz =>
    A.interimAllocProb_nonneg_of_isFeasible hfeas i z
