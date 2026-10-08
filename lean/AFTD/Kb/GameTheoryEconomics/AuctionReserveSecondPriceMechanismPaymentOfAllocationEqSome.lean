import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceAllocation
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceMechanism
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceClearingPrice
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceMechanismPaymentRule
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceMechanismAllocationRule

/-!
# Auction.ReserveSecondPrice.mechanism_payment_of_allocation_eq_some

Topic: mechanism_design   Node: 03337012f542

Provenance: formalization of a published result. Source: EconCSLib, `Auction.ReserveSecondPrice.mechanism_payment_of_allocation_eq_some`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/ReserveVickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The allocated bidder pays the clearing price.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
variable {reserve : U} {v : I → U} in
omit [IsOrderedAddMonoid U] in
/-- The allocated bidder pays the clearing price. -/
lemma Auction.ReserveSecondPrice.mechanism_payment_of_allocation_eq_some {reserve : U} {b : I → U} {i : I}
    (halloc : allocation reserve b = some i) :
    (mechanism reserve).paymentRule b i = clearingPrice reserve b := by
  rw [mechanism_paymentRule, if_pos halloc]
