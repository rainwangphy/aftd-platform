import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionFirstPriceWinner
import AFTD.Kb.GameTheoryEconomics.AuctionFirstPriceUtility

/-!
# Auction.FirstPrice.utility_loser

Topic: mechanism_design   Node: c4d05a9ca20a

Provenance: formalization of a published result. Source: EconCSLib, `Auction.FirstPrice.utility_loser`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/FirstPrice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If `i` is not the winner, utility is `0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
variable {v : I → U} in
omit [IsOrderedAddMonoid U] in
/-- If `i` is not the winner, utility is `0`. -/
lemma Auction.FirstPrice.utility_loser {b : I → U} {i : I} (h : i ≠ winner b) :
    utility v b i = 0 := if_neg h
