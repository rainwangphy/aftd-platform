import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceAllocation
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceWinner

/-!
# Auction.ReserveSecondPrice.allocation_eq_none_iff

Topic: mechanism_design   Node: d16db4898087

Provenance: formalization of a published result. Source: EconCSLib, `Auction.ReserveSecondPrice.allocation_eq_none_iff`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/ReserveVickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The item is withheld exactly when the winning bid is below the reserve.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
omit [DecidableEq I] [AddCommGroup U] [IsOrderedAddMonoid U] in
/-- The item is withheld exactly when the winning bid is below the reserve. -/
lemma Auction.ReserveSecondPrice.allocation_eq_none_iff {reserve : U} {b : I → U} :
    allocation reserve b = none ↔ b (SecondPrice.winner b) < reserve := by
  unfold allocation
  by_cases h : reserve ≤ b (SecondPrice.winner b)
  · simp [h, not_lt_of_ge h]
  · have hlt : b (SecondPrice.winner b) < reserve := lt_of_not_ge h
    simp [h, hlt]
