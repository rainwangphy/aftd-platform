import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceAllocation
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceWinner

/-!
# Auction.ReserveSecondPrice.winner_eq_of_allocation_eq_some

Topic: mechanism_design   Node: f1111c39551d

Provenance: formalization of a published result. Source: EconCSLib, `Auction.ReserveSecondPrice.winner_eq_of_allocation_eq_some`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/ReserveVickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If bidder `i` is allocated the item, then `i` is the second-price winner.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
omit [DecidableEq I] [AddCommGroup U] [IsOrderedAddMonoid U] in
/-- If bidder `i` is allocated the item, then `i` is the second-price winner. -/
lemma Auction.ReserveSecondPrice.winner_eq_of_allocation_eq_some {reserve : U} {b : I → U} {i : I}
    (halloc : allocation reserve b = some i) :
    SecondPrice.winner b = i := by
  unfold allocation at halloc
  by_cases h : reserve ≤ b (SecondPrice.winner b)
  · simpa [h] using halloc
  · simp [h] at halloc
