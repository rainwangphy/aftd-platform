import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceWinner
import AFTD.Kb.GameTheoryEconomics.AuctionBidLeMaxBid

/-!
# Auction.SecondPrice.bid_le_bid_winner

Topic: mechanism_design   Node: 8deb3c5a08fb

Provenance: formalization of a published result. Source: EconCSLib, `Auction.SecondPrice.bid_le_bid_winner`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Vickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Auction.SecondPrice.bid_le_bid_winner
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
omit [DecidableEq I] [AddCommGroup U] [IsOrderedAddMonoid U] in
lemma Auction.SecondPrice.bid_le_bid_winner (b : I → U) (j : I) : b j ≤ b (winner b) :=
  Auction.bid_le_maxBid b j
