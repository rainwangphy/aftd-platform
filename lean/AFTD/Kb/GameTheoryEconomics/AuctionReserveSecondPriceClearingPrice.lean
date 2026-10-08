import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceSecondPrice

/-!
# Auction.ReserveSecondPrice.clearingPrice

Topic: mechanism_design   Node: 92deaa51a724

Provenance: formalization of a published result. Source: EconCSLib, `Auction.ReserveSecondPrice.clearingPrice`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/ReserveVickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The price paid by the winner: the maximum of the reserve and the second price.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
/-- The price paid by the winner: the maximum of the reserve and the second price. -/
noncomputable def Auction.ReserveSecondPrice.clearingPrice (reserve : U) (b : I → U) : U :=
  max reserve (SecondPrice.secondPrice b)
