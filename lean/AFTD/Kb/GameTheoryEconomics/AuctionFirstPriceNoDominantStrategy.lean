import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsWeaklyDominant
import AFTD.Kb.GameTheoryEconomics.AuctionFirstPriceGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameDeviate
import AFTD.Kb.GameTheoryEconomics.AuctionFirstPriceWinner
import AFTD.Kb.GameTheoryEconomics.AuctionFirstPriceEqWinnerOfBidGt
import AFTD.Kb.GameTheoryEconomics.AuctionFirstPriceUtility
import AFTD.Kb.GameTheoryEconomics.AuctionFirstPriceUtilityWinner
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe

/-!
# Auction.FirstPrice.no_dominant_strategy

Topic: mechanism_design   Node: dd6fa8131b27

Provenance: formalization of a published result. Source: EconCSLib, `Auction.FirstPrice.no_dominant_strategy`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/FirstPrice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**No dominant strategy exists in first-price auctions.** For any bidder `i` and any bid `bi`, there exists a profile where bidding `bi` is not optimal for `i`. Counterexample (from xmum/gametheory): set all opponents to bid `bi − a` for some `a > 0`, then `i` wins with both `bi` and `bi − a` but pays less with `bi − a`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Auction Auction.FirstPrice in
variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I] in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
variable {v : I → U} in
/-- **No dominant strategy exists in first-price auctions.** For any bidder `i` and any bid `bi`, there exists a profile where bidding `bi` is not optimal for `i`. Counterexample (from xmum/gametheory): set all opponents to bid `bi − a` for some `a > 0`, then `i` wins with both `bi` and `bi − a` but pays less with `bi − a`. -/
theorem Auction.FirstPrice.no_dominant_strategy (v : I → U) (i : I) (bi : U)
    (ha : ∃ a : U, 0 < a) :
    ¬ IsWeaklyDominant (game v) i bi := by
  obtain ⟨a, ha⟩ := ha
  intro hdom
  -- Counterexample: others bid (bi - 2a), i bids (bi - a) vs bi.
  -- i wins both ways, but pays less with (bi - a), contradicting dominance of bi.
  set b : I → U := Function.update (fun _ => bi - a - a) i (bi - a)
  have hwd := hdom (bi - a) b
  have hb_other : ∀ j, j ≠ i → b j = bi - a - a := by
    intro j hj; exact Function.update_of_ne hj _ _
  have hb_self : b i = bi - a := by simp [b, Function.update_self]
  -- bi - a - a < bi - a since a > 0
  have hlt_a : bi - a - a < bi - a := sub_lt_self _ ha
  have hi_wins_b : i = winner b := by
    apply eq_winner_of_bid_gt
    intro j hj
    rw [hb_other j hj, hb_self]
    exact hlt_a
  -- bi - a - a < bi since a > 0
  have hlt_bi : bi - a - a < bi := lt_trans hlt_a (sub_lt_self _ ha)
  have hi_wins_bi : i = winner (Function.update b i bi) := by
    apply eq_winner_of_bid_gt
    intro j hj
    rw [Function.update_of_ne hj, hb_other j hj, Function.update_self]
    exact hlt_bi
  -- Compute both payoffs
  have h1 : (game v).payoff (Function.update b i (bi - a)) i = v i - (bi - a) := by
    show utility v (Function.update b i (bi - a)) i = _
    rw [show Function.update b i (bi - a) = b from by
      simp [b, Function.update_idem]]
    rw [utility_winner hi_wins_b]
    simp [b, Function.update_self]
  have h2 : (game v).payoff (Function.update b i bi) i = v i - bi := by
    show utility v (Function.update b i bi) i = _
    rw [utility_winner hi_wins_bi]
    simp [Function.update_self]
  rw [h1, h2] at hwd
  -- hwd : v i - (bi - a) ≤ v i - bi
  -- i.e. v i - bi + a ≤ v i - bi, i.e. a ≤ 0, contradicting ha
  have : v i - bi < v i - (bi - a) := by
    rw [show v i - (bi - a) = v i - bi + a from by abel]
    exact lt_add_of_pos_right _ ha
  exact absurd hwd (not_le.mpr this)
