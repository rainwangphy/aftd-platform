import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingWinner
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualScore
import AFTD.Kb.GameTheoryEconomics.AuctionBidLeMaxBid
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualValue
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
# BayesianSingleItemAuction.virtualSurplusMaximizingWinner_eq_iff_forall_virtualScore_le

Topic: mechanism_design   Node: 59aad0ed7e2e

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.virtualSurplusMaximizingWinner_eq_iff_forall_virtualScore_le`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/OptimalSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The selected winner is exactly the bidder whose lexicographic virtual score dominates every other bidder's score.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open scoped BigOperators in
open MeasureTheory in
variable {I : Type*} in
/-- The selected winner is exactly the bidder whose lexicographic virtual score dominates every other bidder's score. -/
theorem BayesianSingleItemAuction.virtualSurplusMaximizingWinner_eq_iff_forall_virtualScore_le
    [Fintype I] [Nontrivial I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ) (i : I) :
    A.virtualSurplusMaximizingWinner b = i ↔
      ∀ j, A.virtualScore b j ≤ A.virtualScore b i := by
  constructor
  · intro hwinner j
    have hle :
        A.virtualScore b j ≤
          A.virtualScore b (A.virtualSurplusMaximizingWinner b) := by
      simpa [virtualSurplusMaximizingWinner] using
        Auction.bid_le_maxBid (A.virtualScore b) j
    simpa [hwinner] using hle
  · intro hmax
    let w := A.virtualSurplusMaximizingWinner b
    have hwi : A.virtualScore b w ≤ A.virtualScore b i := hmax w
    have hiw : A.virtualScore b i ≤ A.virtualScore b w := by
      simpa [w, virtualSurplusMaximizingWinner] using
        Auction.bid_le_maxBid (A.virtualScore b) i
    have hscore : A.virtualScore b w = A.virtualScore b i := le_antisymm hwi hiw
    have hpair :
        (A.virtualValue w (b w), w) = (A.virtualValue i (b i), i) := by
      apply toLex_inj.mp
      simpa [w, virtualScore] using hscore
    exact congrArg Prod.snd hpair
