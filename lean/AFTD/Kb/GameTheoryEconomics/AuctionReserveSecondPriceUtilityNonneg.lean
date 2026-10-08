import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceUtility
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceAllocation
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceClearingPrice
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceUtilityWinner
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceClearingPriceLeBidOfAllocationEqSome
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceUtilityLoser

/-!
# Auction.ReserveSecondPrice.utility_nonneg

Topic: mechanism_design   Node: 3ae23d7a8287

Provenance: formalization of a published result. Source: EconCSLib, `Auction.ReserveSecondPrice.utility_nonneg`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/ReserveVickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Truthful bidding yields nonnegative utility.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
variable {reserve : U} {v : I → U} in
/-- Truthful bidding yields nonnegative utility. -/
lemma Auction.ReserveSecondPrice.utility_nonneg {b : I → U} {i : I} (htruth : b i = v i) :
    0 ≤ utility reserve v b i := by
  by_cases halloc : allocation reserve b = some i
  · rw [utility_winner halloc, sub_nonneg, ← htruth]
    exact clearingPrice_le_bid_of_allocation_eq_some halloc
  · simp [utility_loser halloc]
