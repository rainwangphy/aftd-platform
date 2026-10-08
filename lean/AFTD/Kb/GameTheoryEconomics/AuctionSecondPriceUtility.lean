import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceWinner
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceSecondPrice

/-!
# Auction.SecondPrice.utility

Topic: mechanism_design   Node: fb79b3d7f38e

Provenance: formalization of a published result. Source: EconCSLib, `Auction.SecondPrice.utility`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Vickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Utility of bidder `i` in a second-price auction: winner gets `v i − secondPrice b`, losers get `0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
/-- Utility of bidder `i` in a second-price auction: winner gets `v i − secondPrice b`, losers get `0`. -/
noncomputable def Auction.SecondPrice.utility (v b : I → U) (i : I) : U :=
  if i = winner b then v i - secondPrice b else 0
