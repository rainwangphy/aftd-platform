import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBid
import AFTD.Kb.GameTheoryEconomics.AuctionExistsMaxBid

/-!
# Auction.argmaxBid

Topic: mechanism_design   Node: 1452c6d29627

Provenance: formalization of a published result. Source: EconCSLib, `Auction.argmaxBid`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/AuctionBasic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The bidder whose bid achieves the maximum. This is a mathematical argmax, not a declaration that any auction's winner is the highest bidder. Concrete auctions define their own allocation/winner rules.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] {V : Type*} [LinearOrder V] in
variable (b : I → V) in
/-- The bidder whose bid achieves the maximum. This is a mathematical argmax, not a declaration that any auction's winner is the highest bidder. Concrete auctions define their own allocation/winner rules. -/
noncomputable def Auction.argmaxBid : I := Classical.choose (exists_maxBid b)
