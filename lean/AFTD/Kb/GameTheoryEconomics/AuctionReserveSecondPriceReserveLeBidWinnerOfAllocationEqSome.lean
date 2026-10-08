import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceAllocation
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceWinner

/-!
# Auction.ReserveSecondPrice.reserve_le_bid_winner_of_allocation_eq_some

Topic: mechanism_design   Node: 7315d74000f4

Provenance: formalization of a published result. Source: EconCSLib, `Auction.ReserveSecondPrice.reserve_le_bid_winner_of_allocation_eq_some`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/ReserveVickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If the item is allocated, then the winning bid meets the reserve.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
omit [DecidableEq I] [AddCommGroup U] [IsOrderedAddMonoid U] in
/-- If the item is allocated, then the winning bid meets the reserve. -/
lemma Auction.ReserveSecondPrice.reserve_le_bid_winner_of_allocation_eq_some {reserve : U} {b : I → U} {i : I}
    (halloc : allocation reserve b = some i) :
    reserve ≤ b (SecondPrice.winner b) := by
  unfold allocation at halloc
  by_cases h : reserve ≤ b (SecondPrice.winner b)
  · exact h
  · simp [h] at halloc
