import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceMechanism
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceAllocation

/-!
# Auction.ReserveSecondPrice.mechanism_allocationRule

Topic: mechanism_design   Node: 99659187c280

Provenance: formalization of a published result. Source: EconCSLib, `Auction.ReserveSecondPrice.mechanism_allocationRule`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/ReserveVickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Auction.ReserveSecondPrice.mechanism_allocationRule
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
variable {reserve : U} {v : I → U} in
omit [IsOrderedAddMonoid U] in
@[simp] lemma Auction.ReserveSecondPrice.mechanism_allocationRule (reserve : U) (b : I → U) :
    (mechanism reserve).allocationRule b = allocation reserve b :=
  rfl
