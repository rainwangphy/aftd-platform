import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceAllocation
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceClearingPrice

/-!
# Auction.ReserveSecondPrice.mechanism

Topic: mechanism_design   Node: 3d387dad6299

Provenance: formalization of a published result. Source: EconCSLib, `Auction.ReserveSecondPrice.mechanism`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/ReserveVickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The reserve second-price auction as a `MechanismWithTransfers`. Agents report bids in `U`. The allocation is `none` when the reserve is not met, and `some i` when bidder `i` receives the item.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
variable {reserve : U} {v : I → U} in
/-- The reserve second-price auction as a `MechanismWithTransfers`. Agents report bids in `U`. The allocation is `none` when the reserve is not met, and `some i` when bidder `i` receives the item. -/
noncomputable def Auction.ReserveSecondPrice.mechanism (reserve : U) :
    MechanismWithTransfers I (fun _ => U) (Option I) U where
  allocationRule b := allocation reserve b
  paymentRule b i := if allocation reserve b = some i then clearingPrice reserve b else 0
