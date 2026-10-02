import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsSimpleGame
import AFTD.Kb.GameTheoryEconomics.SwingTable
import AFTD.Kb.GameTheoryEconomics.SimpleGameCardSizeEqOfSwingTableEq
import AFTD.Kb.GameTheoryEconomics.CardFilterEqSumRangeCardSize

/-!
# simple_game_card_winning_eq_of_swing_table_eq

Topic: general_equilibrium   Node: dc6906629e85

If two simple games have the same swing table, they have the same number of winning coalitions.
-/

/-- Two simple games with the same swing table have the same number of winning coalitions. -/
theorem simple_game_card_winning_eq_of_swing_table_eq {n : ℕ} (f g : Finset (Fin n) → Bool)
    (hf : is_simple_game f) (hg : is_simple_game g)
    (h : ∀ i k, swing_table f i k = swing_table g i k) :
    (Finset.univ.filter fun S : Finset (Fin n) => f S = true).card
      = (Finset.univ.filter fun S : Finset (Fin n) => g S = true).card := by
  rw [card_filter_eq_sum_range_card_size f, card_filter_eq_sum_range_card_size g]
  exact Finset.sum_congr rfl fun k _ => simple_game_card_size_eq_of_swing_table_eq f g hf hg h k
