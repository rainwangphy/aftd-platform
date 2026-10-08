import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceUtility
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceWinner
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceSecondPrice
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceUtilityWinner
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceSecondPriceLeBidWinner
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceUtilityLoser

/-!
# Auction.SecondPrice.utility_nonneg

Topic: mechanism_design   Node: 9b49371919cd

Provenance: formalization of a published result. Source: EconCSLib, `Auction.SecondPrice.utility_nonneg`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Vickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Truthful bidding yields nonneg utility.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
variable {v : I → U} in
/-- Truthful bidding yields nonneg utility. -/
lemma Auction.SecondPrice.utility_nonneg {b : I → U} {i : I} (htruth : b i = v i) :
    0 ≤ utility v b i := by
  rcases eq_or_ne i (winner b) with rfl | hne
  · rw [utility_winner rfl, sub_nonneg, ← htruth]
    exact secondPrice_le_bid_winner b
  · simp [utility_loser hne]
