import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionArgmaxBid

/-!
# Auction.FirstPrice.winner

Topic: mechanism_design   Node: 5520c93c99e5

Provenance: formalization of a published result. Source: EconCSLib, `Auction.FirstPrice.winner`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/FirstPrice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The winner of the first-price auction: the bidder with the highest bid. Uses `Auction.argmaxBid` from `MechanismDesign.Auction.AuctionBasic`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
/-- The winner of the first-price auction: the bidder with the highest bid. Uses `Auction.argmaxBid` from `MechanismDesign.Auction.AuctionBasic`. -/
noncomputable def Auction.FirstPrice.winner (b : I → U) : I := Auction.argmaxBid b
