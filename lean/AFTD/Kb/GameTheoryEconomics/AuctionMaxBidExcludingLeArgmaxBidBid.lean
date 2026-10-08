import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionArgmaxBid
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBidExcludingLeMaxBid
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBidExcluding
import AFTD.Kb.GameTheoryEconomics.AuctionArgmaxBidEqMaxBid
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBid

/-!
# Auction.maxBidExcluding_le_argmaxBid_bid

Topic: mechanism_design   Node: 6a9399ff4f82

Provenance: formalization of a published result. Source: EconCSLib, `Auction.maxBidExcluding_le_argmaxBid_bid`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/AuctionBasic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The argmax bidder's bid is at least the highest bid among all others.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] {V : Type*} [LinearOrder V] in
variable (b : I → V) in
variable [DecidableEq I] in
/-- The argmax bidder's bid is at least the highest bid among all others. -/
lemma Auction.maxBidExcluding_le_argmaxBid_bid :
    maxBidExcluding b (argmaxBid b) ≤ b (argmaxBid b) := by
  calc maxBidExcluding b (argmaxBid b)
      ≤ maxBid b := maxBidExcluding_le_maxBid b (argmaxBid b)
    _ = b (argmaxBid b) := (argmaxBid_eq_maxBid b).symm
