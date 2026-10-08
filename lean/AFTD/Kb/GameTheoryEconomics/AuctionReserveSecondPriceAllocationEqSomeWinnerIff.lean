import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceAllocation
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceWinner

/-!
# Auction.ReserveSecondPrice.allocation_eq_some_winner_iff

Topic: mechanism_design   Node: 0cfc09c6bd8a

Provenance: formalization of a published result. Source: EconCSLib, `Auction.ReserveSecondPrice.allocation_eq_some_winner_iff`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/ReserveVickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The allocation is the second-price winner exactly when the winner's bid meets the reserve.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
omit [DecidableEq I] [AddCommGroup U] [IsOrderedAddMonoid U] in
/-- The allocation is the second-price winner exactly when the winner's bid meets the reserve. -/
lemma Auction.ReserveSecondPrice.allocation_eq_some_winner_iff {reserve : U} {b : I → U} :
    allocation reserve b = some (SecondPrice.winner b) ↔
      reserve ≤ b (SecondPrice.winner b) := by
  unfold allocation
  by_cases h : reserve ≤ b (SecondPrice.winner b) <;> simp [h]
