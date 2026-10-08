import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceAllocation
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceUtility
import AFTD.Kb.GameTheoryEconomics.AuctionReserveSecondPriceClearingPrice

/-!
# Auction.ReserveSecondPrice.utility_loser

Topic: mechanism_design   Node: 042c297a872f

Provenance: formalization of a published result. Source: EconCSLib, `Auction.ReserveSecondPrice.utility_loser`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/ReserveVickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Auction.ReserveSecondPrice.utility_loser
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
variable {reserve : U} {v : I → U} in
omit [IsOrderedAddMonoid U] in
lemma Auction.ReserveSecondPrice.utility_loser {b : I → U} {i : I} (h : allocation reserve b ≠ some i) :
    utility reserve v b i = 0 := if_neg h
