import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceWinner
import AFTD.Kb.GameTheoryEconomics.AuctionEqArgmaxBidOfStrictMax

/-!
# Auction.SecondPrice.eq_winner_of_bid_gt

Topic: mechanism_design   Node: 479639370669

Provenance: formalization of a published result. Source: EconCSLib, `Auction.SecondPrice.eq_winner_of_bid_gt`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Vickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Auction.SecondPrice.eq_winner_of_bid_gt
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
omit [DecidableEq I] [AddCommGroup U] [IsOrderedAddMonoid U] in
lemma Auction.SecondPrice.eq_winner_of_bid_gt {b : I → U} (i : I) (h : ∀ j, j ≠ i → b j < b i) :
    i = winner b :=
  Auction.eq_argmaxBid_of_strict_max b i h
