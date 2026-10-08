import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceAllocation
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceClearingPrice
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceWinner
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceWinnerEqOfAllocationEqSome
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceReserveLeBidWinnerOfAllocationEqSome
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceSecondPrice
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceSecondPriceLeBidWinner

/-!
# Auction.ReserveSecondPrice.clearingPrice_le_bid_of_allocation_eq_some

Topic: mechanism_design   Node: 8546b427c219

Provenance: formalization of a published result. Source: EconCSLib, `Auction.ReserveSecondPrice.clearingPrice_le_bid_of_allocation_eq_some`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/ReserveVickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

When the item is sold, the clearing price is no more than the allocated bidder's bid.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
omit [AddCommGroup U] [IsOrderedAddMonoid U] in
/-- When the item is sold, the clearing price is no more than the allocated bidder's bid. -/
lemma Auction.ReserveSecondPrice.clearingPrice_le_bid_of_allocation_eq_some {reserve : U} {b : I → U} {i : I}
    (halloc : allocation reserve b = some i) :
    clearingPrice reserve b ≤ b i := by
  have hwinner : SecondPrice.winner b = i := winner_eq_of_allocation_eq_some halloc
  have hreserve : reserve ≤ b i := by
    have h := reserve_le_bid_winner_of_allocation_eq_some halloc
    simpa [hwinner] using h
  have hsecond : SecondPrice.secondPrice b ≤ b i := by
    simpa [hwinner] using SecondPrice.secondPrice_le_bid_winner (b := b)
  exact max_le hreserve hsecond
