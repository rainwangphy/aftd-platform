import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIsRegular
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingWinner
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualScore
import AFTD.Kb.GameTheoryEconomics.AuctionArgmaxBid
import AFTD.Kb.GameTheoryEconomics.AuctionBidLeMaxBid
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualValue
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualScoreUpdateSelfMonoOfIsRegular
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualScoreUpdateNe
import AFTD.Kb.GameTheoryEconomics.AuctionEqArgmaxBidOfStrictMax
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
# BayesianSingleItemAuction.virtualSurplusMaximizingWinner_update_self_of_winner

Topic: mechanism_design   Node: 82c3ff41b97b

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.virtualSurplusMaximizingWinner_update_self_of_winner`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/OptimalSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

BayesianSingleItemAuction.virtualSurplusMaximizingWinner_update_self_of_winner
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open scoped BigOperators in
open MeasureTheory in
variable {I : Type*} in
lemma BayesianSingleItemAuction.virtualSurplusMaximizingWinner_update_self_of_winner
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.IsRegular)
    (b : I → ℝ) (i : I) {r s : ℝ} (hrs : r ≤ s)
    (hwinner : A.virtualSurplusMaximizingWinner (Function.update b i r) = i) :
    A.virtualSurplusMaximizingWinner (Function.update b i s) = i := by
  classical
  let bLo := Function.update b i r
  let bHi := Function.update b i s
  have hstrict : ∀ j, j ≠ i → A.virtualScore bHi j < A.virtualScore bHi i := by
    intro j hji
    have hwinner' : Auction.argmaxBid (A.virtualScore bLo) = i := by
      simpa [virtualSurplusMaximizingWinner, bLo] using hwinner
    have hle_lo :
        A.virtualScore bLo j ≤ A.virtualScore bLo i := by
      simpa [hwinner'] using
        Auction.bid_le_maxBid (A.virtualScore bLo) j
    have hne_lo : A.virtualScore bLo j ≠ A.virtualScore bLo i := by
      intro h
      exact hji (Prod.ext_iff.mp (toLex_inj.mp h)).2
    have hlt_lo : A.virtualScore bLo j < A.virtualScore bLo i :=
      lt_of_le_of_ne hle_lo hne_lo
    have hle_self : A.virtualScore bLo i ≤ A.virtualScore bHi i := by
      simpa [bLo, bHi] using
        A.virtualScore_update_self_mono_of_isRegular hA b i hrs
    have hlt_hi : A.virtualScore bLo j < A.virtualScore bHi i :=
      lt_of_lt_of_le hlt_lo hle_self
    simpa [bLo, bHi, virtualScore_update_ne A b hji s,
      virtualScore_update_ne A b hji r] using hlt_hi
  exact (Auction.eq_argmaxBid_of_strict_max (A.virtualScore bHi) i hstrict).symm
