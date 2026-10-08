import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBidExcluding
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceWinner

/-!
# Auction.SecondPrice.secondPrice

Topic: mechanism_design   Node: 9f57c7f6409b

Provenance: formalization of a published result. Source: EconCSLib, `Auction.SecondPrice.secondPrice`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Vickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The second price: the highest bid among all bidders other than the winner.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
/-- The second price: the highest bid among all bidders other than the winner. -/
noncomputable def Auction.SecondPrice.secondPrice (b : I → U) : U := Auction.maxBidExcluding b (winner b)
