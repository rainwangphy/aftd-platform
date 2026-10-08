import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionFirstPriceWinner

/-!
# Auction.FirstPrice.utility

Topic: mechanism_design   Node: f31ef6e70231

Provenance: formalization of a published result. Source: EconCSLib, `Auction.FirstPrice.utility`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/FirstPrice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Utility of bidder `i` in a first-price auction: winner gets `v i − b i` (pays own bid), losers get `0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
/-- Utility of bidder `i` in a first-price auction: winner gets `v i − b i` (pays own bid), losers get `0`. -/
noncomputable def Auction.FirstPrice.utility (v b : I → U) (i : I) : U :=
  if i = winner b then v i - b i else 0
