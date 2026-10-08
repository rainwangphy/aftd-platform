import AFTD.Prelude

/-!
# Auction.maxBid

Topic: mechanism_design   Node: ddcfd57a6604

Provenance: formalization of a published result. Source: EconCSLib, `Auction.maxBid`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/AuctionBasic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The highest bid in a profile.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] {V : Type*} [LinearOrder V] in
variable (b : I → V) in
/-- The highest bid in a profile. -/
@[simp]
def Auction.maxBid : V := Finset.sup' Finset.univ Finset.univ_nonempty b
