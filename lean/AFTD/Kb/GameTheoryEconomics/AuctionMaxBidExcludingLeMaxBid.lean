import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBidExcluding
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBid
import AFTD.Kb.Tcs.V

/-!
# Auction.maxBidExcluding_le_maxBid

Topic: mechanism_design   Node: 1ca10841a4b7

Provenance: formalization of a published result. Source: EconCSLib, `Auction.maxBidExcluding_le_maxBid`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/AuctionBasic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Excluding any bidder can only decrease the highest bid.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] {V : Type*} [LinearOrder V] in
variable (b : I → V) in
variable [DecidableEq I] in
/-- Excluding any bidder can only decrease the highest bid. -/
lemma Auction.maxBidExcluding_le_maxBid (i : I) : maxBidExcluding b i ≤ maxBid b := by
  apply Finset.sup'_mono
  exact Finset.subset_univ _
