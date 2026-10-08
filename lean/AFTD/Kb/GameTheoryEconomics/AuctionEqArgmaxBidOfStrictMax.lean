import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionArgmaxBid
import AFTD.Kb.GameTheoryEconomics.AuctionBidLeMaxBid
import AFTD.Kb.Tcs.V

/-!
# Auction.eq_argmaxBid_of_strict_max

Topic: mechanism_design   Node: e938bf260415

Provenance: formalization of a published result. Source: EconCSLib, `Auction.eq_argmaxBid_of_strict_max`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/AuctionBasic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If `i` strictly outbids all others, then `i` is the argmax bidder.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] {V : Type*} [LinearOrder V] in
variable (b : I → V) in
/-- If `i` strictly outbids all others, then `i` is the argmax bidder. -/
lemma Auction.eq_argmaxBid_of_strict_max (i : I) (h : ∀ j, j ≠ i → b j < b i) :
    i = argmaxBid b := by
  contrapose! h
  exact ⟨argmaxBid b, h.symm, bid_le_maxBid b i⟩
