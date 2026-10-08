import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceWinner

/-!
# Auction.ReserveSecondPrice.allocation

Topic: mechanism_design   Node: 671cdfab1de0

Provenance: formalization of a published result. Source: EconCSLib, `Auction.ReserveSecondPrice.allocation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/ReserveVickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The item is sold exactly when the winning bid meets the reserve.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
/-- The item is sold exactly when the winning bid meets the reserve. -/
noncomputable def Auction.ReserveSecondPrice.allocation (reserve : U) (b : I → U) : Option I :=
  if reserve ≤ b (SecondPrice.winner b) then some (SecondPrice.winner b) else none
