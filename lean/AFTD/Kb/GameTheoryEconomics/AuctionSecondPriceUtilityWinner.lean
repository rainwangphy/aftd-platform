import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceWinner
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceUtility
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceSecondPrice

/-!
# Auction.SecondPrice.utility_winner

Topic: mechanism_design   Node: 743549aa9d6d

Provenance: formalization of a published result. Source: EconCSLib, `Auction.SecondPrice.utility_winner`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Vickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If `i` is the winner, utility is `v i − secondPrice b`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
variable {v : I → U} in
omit [IsOrderedAddMonoid U] in
/-- If `i` is the winner, utility is `v i − secondPrice b`. -/
lemma Auction.SecondPrice.utility_winner {b : I → U} {i : I} (h : i = winner b) :
    utility v b i = v i - secondPrice b := if_pos h
