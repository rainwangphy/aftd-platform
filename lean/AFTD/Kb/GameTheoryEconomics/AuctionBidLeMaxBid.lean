import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionArgmaxBid
import AFTD.Kb.GameTheoryEconomics.AuctionArgmaxBidEqMaxBid
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBid

/-!
# Auction.bid_le_maxBid

Topic: mechanism_design   Node: 11b8f6b07b64

Provenance: formalization of a published result. Source: EconCSLib, `Auction.bid_le_maxBid`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/AuctionBasic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every bid is at most the argmax bidder's bid.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] {V : Type*} [LinearOrder V] in
variable (b : I → V) in
/-- Every bid is at most the argmax bidder's bid. -/
lemma Auction.bid_le_maxBid (j : I) : b j ≤ b (argmaxBid b) := by
  rw [argmaxBid_eq_maxBid b]
  exact Finset.le_sup' b (Finset.mem_univ j)
