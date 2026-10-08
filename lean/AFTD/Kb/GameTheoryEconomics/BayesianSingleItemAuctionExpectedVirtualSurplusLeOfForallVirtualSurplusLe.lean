import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIntegrableVirtualSurplus
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplus
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionExpectedVirtualSurplus
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
# BayesianSingleItemAuction.expectedVirtualSurplus_le_of_forall_virtualSurplus_le

Topic: mechanism_design   Node: 29971b72ac96

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.expectedVirtualSurplus_le_of_forall_virtualSurplus_le`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/OptimalSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Pointwise virtual-surplus dominance lifts to ex-ante dominance.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open scoped BigOperators in
open MeasureTheory in
variable {I : Type*} in
/-- Pointwise virtual-surplus dominance lifts to ex-ante dominance. -/
theorem BayesianSingleItemAuction.expectedVirtualSurplus_le_of_forall_virtualSurplus_le [Fintype I]
    (A : BayesianSingleItemAuction I) {x y : (I → ℝ) → I → ℝ}
    (hx_int : A.IntegrableVirtualSurplus x)
    (hy_int : A.IntegrableVirtualSurplus y)
    (hxy : ∀ t, A.virtualSurplus x t ≤ A.virtualSurplus y t) :
    A.expectedVirtualSurplus x ≤ A.expectedVirtualSurplus y :=
  integral_mono hx_int hy_int hxy
