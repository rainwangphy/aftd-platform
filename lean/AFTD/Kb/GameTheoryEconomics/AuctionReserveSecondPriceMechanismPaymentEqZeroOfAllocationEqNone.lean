import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceAllocation
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceMechanism
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceMechanismPaymentOfAllocationNeSome
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceMechanismAllocationRule
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceMechanismPaymentRule

/-!
# Auction.ReserveSecondPrice.mechanism_payment_eq_zero_of_allocation_eq_none

Topic: mechanism_design   Node: cec29db2acd7

Provenance: formalization of a published result. Source: EconCSLib, `Auction.ReserveSecondPrice.mechanism_payment_eq_zero_of_allocation_eq_none`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/ReserveVickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If the item is withheld, every bidder pays zero.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
variable {reserve : U} {v : I → U} in
omit [IsOrderedAddMonoid U] in
/-- If the item is withheld, every bidder pays zero. -/
lemma Auction.ReserveSecondPrice.mechanism_payment_eq_zero_of_allocation_eq_none {reserve : U} {b : I → U} {i : I}
    (halloc : allocation reserve b = none) :
    (mechanism reserve).paymentRule b i = 0 := by
  exact mechanism_payment_of_allocation_ne_some (by intro h; simp [halloc] at h)
