import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionArgmaxBid
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBidExcluding
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBid
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBidExcludingLeMaxBid
import AFTD.Kb.GameTheoryEconomics.AuctionArgmaxBidEqMaxBid
import AFTD.Kb.Tcs.V

/-!
# Auction.maxBidExcluding_eq_maxBid_of_not_argmax

Topic: mechanism_design   Node: b44ab4cb2e8b

Provenance: formalization of a published result. Source: EconCSLib, `Auction.maxBidExcluding_eq_maxBid_of_not_argmax`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/AuctionBasic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If `i` is not the argmax bidder, excluding `i` does not change the highest bid.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] {V : Type*} [LinearOrder V] in
variable (b : I → V) in
variable [DecidableEq I] in
/-- If `i` is not the argmax bidder, excluding `i` does not change the highest bid. -/
lemma Auction.maxBidExcluding_eq_maxBid_of_not_argmax {i : I} (h : i ≠ argmaxBid b) :
    maxBidExcluding b i = maxBid b := by
  apply le_antisymm
  · exact maxBidExcluding_le_maxBid b i
  · rw [← argmaxBid_eq_maxBid b]
    exact Finset.le_sup' b (Finset.mem_erase_of_ne_of_mem h.symm (Finset.mem_univ _))
