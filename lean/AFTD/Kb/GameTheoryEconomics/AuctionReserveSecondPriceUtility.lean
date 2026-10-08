import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceAllocation
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceClearingPrice

/-!
# Auction.ReserveSecondPrice.utility

Topic: mechanism_design   Node: 4b66ecda5f3e

Provenance: formalization of a published result. Source: EconCSLib, `Auction.ReserveSecondPrice.utility`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/ReserveVickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Utility of bidder `i`: the allocated bidder receives value minus the clearing price; all others receive `0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
/-- Utility of bidder `i`: the allocated bidder receives value minus the clearing price; all others receive `0`. -/
noncomputable def Auction.ReserveSecondPrice.utility (reserve : U) (v b : I → U) (i : I) : U :=
  if allocation reserve b = some i then v i - clearingPrice reserve b else 0
