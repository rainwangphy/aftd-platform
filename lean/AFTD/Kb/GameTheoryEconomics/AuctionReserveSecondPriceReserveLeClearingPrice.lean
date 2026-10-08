import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceClearingPrice
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceSecondPrice

/-!
# Auction.ReserveSecondPrice.reserve_le_clearingPrice

Topic: mechanism_design   Node: e03cf2f0e426

Provenance: formalization of a published result. Source: EconCSLib, `Auction.ReserveSecondPrice.reserve_le_clearingPrice`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/ReserveVickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The clearing price is at least the reserve.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
omit [AddCommGroup U] [IsOrderedAddMonoid U] in
/-- The clearing price is at least the reserve. -/
lemma Auction.ReserveSecondPrice.reserve_le_clearingPrice (reserve : U) (b : I → U) :
    reserve ≤ clearingPrice reserve b :=
  le_max_left reserve (SecondPrice.secondPrice b)
