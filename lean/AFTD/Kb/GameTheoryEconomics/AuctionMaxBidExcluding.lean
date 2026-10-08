import AFTD.Prelude
import AFTD.Kb.Tcs.V

/-!
# Auction.maxBidExcluding

Topic: mechanism_design   Node: 51ee10881bc9

Provenance: formalization of a published result. Source: EconCSLib, `Auction.maxBidExcluding`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/AuctionBasic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The highest bid excluding bidder `i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] {V : Type*} [LinearOrder V] in
variable (b : I → V) in
variable [DecidableEq I] in
/-- The highest bid excluding bidder `i`. -/
noncomputable def Auction.maxBidExcluding (i : I) : V :=
  (Finset.univ.erase i).sup' Finset.univ_nontrivial.erase_nonempty b
