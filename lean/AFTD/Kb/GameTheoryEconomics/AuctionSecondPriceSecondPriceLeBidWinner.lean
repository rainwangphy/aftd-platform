import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceSecondPrice
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceWinner
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBidExcluding
import AFTD.Kb.GameTheoryEconomics.AuctionArgmaxBid
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBid
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBidExcludingLeMaxBid
import AFTD.Kb.GameTheoryEconomics.AuctionArgmaxBidEqMaxBid

/-!
# Auction.SecondPrice.secondPrice_le_bid_winner

Topic: mechanism_design   Node: 340055f890cd

Provenance: formalization of a published result. Source: EconCSLib, `Auction.SecondPrice.secondPrice_le_bid_winner`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Vickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The winner's bid is at least the second price.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
omit [AddCommGroup U] [IsOrderedAddMonoid U] in
/-- The winner's bid is at least the second price. -/
lemma Auction.SecondPrice.secondPrice_le_bid_winner (b : I → U) : secondPrice b ≤ b (winner b) := by
  unfold secondPrice winner
  calc Auction.maxBidExcluding b (Auction.argmaxBid b)
      ≤ Auction.maxBid b := Auction.maxBidExcluding_le_maxBid b _
    _ = b (Auction.argmaxBid b) := (Auction.argmaxBid_eq_maxBid b).symm
