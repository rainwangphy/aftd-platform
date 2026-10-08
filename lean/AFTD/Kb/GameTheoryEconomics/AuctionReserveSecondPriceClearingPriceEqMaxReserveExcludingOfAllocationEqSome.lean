import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceAllocation
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceClearingPrice
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBidExcluding
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceWinner
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceWinnerEqOfAllocationEqSome
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceSecondPrice

/-!
# Auction.ReserveSecondPrice.clearingPrice_eq_max_reserve_excluding_of_allocation_eq_some

Topic: mechanism_design   Node: b3e7bdea4ab8

Provenance: formalization of a published result. Source: EconCSLib, `Auction.ReserveSecondPrice.clearingPrice_eq_max_reserve_excluding_of_allocation_eq_some`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/ReserveVickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

When bidder `i` receives the item, the clearing price is the maximum of the reserve and the highest bid excluding `i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
omit [AddCommGroup U] [IsOrderedAddMonoid U] in
/-- When bidder `i` receives the item, the clearing price is the maximum of the reserve and the highest bid excluding `i`. -/
lemma Auction.ReserveSecondPrice.clearingPrice_eq_max_reserve_excluding_of_allocation_eq_some
    {reserve : U} {b : I → U} {i : I}
    (halloc : allocation reserve b = some i) :
    clearingPrice reserve b = max reserve (Auction.maxBidExcluding b i) := by
  have hwinner : SecondPrice.winner b = i := winner_eq_of_allocation_eq_some halloc
  simp [clearingPrice, SecondPrice.secondPrice, hwinner]
