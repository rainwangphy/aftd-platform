import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceWinner
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBidExcluding
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBid
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBidExcludingEqMaxBidOfNotArgmax

/-!
# Auction.SecondPrice.maxBidExcluding_eq_maxBid_if_loser

Topic: mechanism_design   Node: 978048f7233a

Provenance: formalization of a published result. Source: EconCSLib, `Auction.SecondPrice.maxBidExcluding_eq_maxBid_if_loser`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Vickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Auction.SecondPrice.maxBidExcluding_eq_maxBid_if_loser
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
omit [AddCommGroup U] [IsOrderedAddMonoid U] in
lemma Auction.SecondPrice.maxBidExcluding_eq_maxBid_if_loser {b : I → U} {i : I} (h : i ≠ winner b) :
    Auction.maxBidExcluding b i = Auction.maxBid b :=
  Auction.maxBidExcluding_eq_maxBid_of_not_argmax b h
