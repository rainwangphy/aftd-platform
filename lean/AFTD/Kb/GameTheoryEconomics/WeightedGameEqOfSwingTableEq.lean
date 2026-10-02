import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsSimpleGame
import AFTD.Kb.GameTheoryEconomics.IsWeightedGame
import AFTD.Kb.GameTheoryEconomics.SwingTable
import AFTD.Kb.GameTheoryEconomics.SimpleGameCardWinningEqOfSwingTableEq
import AFTD.Kb.GameTheoryEconomics.SimpleGameCardWinningMemEqOfSwingTableEq
import AFTD.Kb.GameTheoryEconomics.WeightedGameEqOfChowParametersEq

/-!
# weighted_game_eq_of_swing_table_eq

Topic: general_equilibrium   Node: 6c918189d386

Fried's swing-rigidity conjecture (arXiv:2607.07013, Conjecture 10.2) is true: if f is a weighted simple game and g is any simple game with the same swing table, then f = g.
-/

/-- Fried's swing-rigidity conjecture (arXiv:2607.07013, Conjecture 10.2) holds: a weighted voting game is determined by its swing table among all simple games. -/
theorem weighted_game_eq_of_swing_table_eq {n : ℕ} (f g : Finset (Fin n) → Bool)
    (hf : is_simple_game f) (hfw : is_weighted_game f) (hg : is_simple_game g)
    (h : ∀ i k, swing_table f i k = swing_table g i k) : f = g :=
  weighted_game_eq_of_chow_parameters_eq f g hfw
    (simple_game_card_winning_eq_of_swing_table_eq f g hf hg h)
    (simple_game_card_winning_mem_eq_of_swing_table_eq f g hf hg h)
