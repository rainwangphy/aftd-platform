import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceWinner
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBid
import AFTD.Kb.GameTheoryEconomics.AuctionArgmaxBidEqMaxBid

/-!
# Auction.SecondPrice.bid_winner_eq_maxBid

Topic: mechanism_design   Node: 62db7cedc32a

Provenance: formalization of a published result. Source: EconCSLib, `Auction.SecondPrice.bid_winner_eq_maxBid`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Vickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Auction.SecondPrice.bid_winner_eq_maxBid
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
omit [DecidableEq I] [AddCommGroup U] [IsOrderedAddMonoid U] in
lemma Auction.SecondPrice.bid_winner_eq_maxBid (b : I → U) : b (winner b) = Auction.maxBid b :=
  Auction.argmaxBid_eq_maxBid b
