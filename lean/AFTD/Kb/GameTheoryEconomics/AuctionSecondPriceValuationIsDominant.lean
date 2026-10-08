import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceUtility
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBidExcluding
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBidExcludingUpdateSelf
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceWinner
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceSecondPrice
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceUtilityWinner
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceUtilityLoser
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceBidLeBidWinner
import AFTD.Kb.GameTheoryEconomics.AuctionMaxBid
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceMaxBidExcludingEqMaxBidIfLoser
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceBidWinnerEqMaxBid
import AFTD.Kb.GameTheoryEconomics.AuctionSecondPriceUtilityNonneg

/-!
# Auction.SecondPrice.valuation_is_dominant

Topic: mechanism_design   Node: 6499b20ae281

Provenance: formalization of a published result. Source: EconCSLib, `Auction.SecondPrice.valuation_is_dominant`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Vickrey.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Vickrey's Theorem** (core form): Truthful bidding dominates any other bid. For any bid profile `b`, replacing `i`'s bid with `v i` does not decrease `i`'s utility.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
variable {v : I → U} in
/-- **Vickrey's Theorem** (core form): Truthful bidding dominates any other bid. For any bid profile `b`, replacing `i`'s bid with `v i` does not decrease `i`'s utility. -/
theorem Auction.SecondPrice.valuation_is_dominant (v : I → U) (i : I) (b : I → U) :
    utility v b i ≤ utility v (Function.update b i (v i)) i := by
  -- Key: maxBidExcluding is unchanged by updating i's bid
  have key : maxBidExcluding (Function.update b i (v i)) i = maxBidExcluding b i :=
    maxBidExcluding_update_self b i (v i)
  by_cases h1 : i = winner b
  · -- Case 1: i wins with current bid b
    rw [utility_winner h1]
    by_cases h2 : i = winner (Function.update b i (v i))
    · -- Case 1a: i also wins with truthful bid — same maxBidExcluding, same payoff
      rw [utility_winner h2, sub_le_sub_iff_left]
      show secondPrice (Function.update b i (v i)) ≤ secondPrice b
      simp only [secondPrice, ← h1, ← h2, key, le_refl]
    · -- Case 1b: i loses with truthful bid — utility becomes 0
      rw [utility_loser h2, sub_nonpos]
      -- Goal: v i ≤ secondPrice b = maxBidExcluding b (winner b) = maxBidExcluding b i
      show v i ≤ secondPrice b
      rw [secondPrice, ← h1]
      -- Goal: v i ≤ maxBidExcluding b i
      set b' := Function.update b i (v i)
      have hle := bid_le_bid_winner b' i
      have hmbe := maxBidExcluding_eq_maxBid_if_loser (b := b') h2
      rw [bid_winner_eq_maxBid b', ← hmbe, key] at hle
      rwa [show b' i = v i from Function.update_self i (v i) b] at hle
  · -- Case 2: i loses with current bid b — utility = 0
    rw [utility_loser h1]
    -- Truthful bid gives nonneg utility
    exact utility_nonneg (Function.update_self i (v i) b)
