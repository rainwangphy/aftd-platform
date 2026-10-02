import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExistsSimpleGamesNeOfSwingTableEq
import AFTD.Kb.GameTheoryEconomics.IsSimpleGame
import AFTD.Kb.GameTheoryEconomics.IsWeightedGame
import AFTD.Kb.GameTheoryEconomics.SwingTable
import AFTD.Kb.GameTheoryEconomics.WeightedGameEqOfSwingTableEq

/-!
# exists_not_weighted_simple_games_ne_of_swing_table_eq

Topic: general_equilibrium   Node: f483139ee703

The weighted hypothesis in swing rigidity cannot be dropped: there are two different five-player simple games, neither of them weighted, with the same swing table.
-/

/-- The weighted hypothesis in swing rigidity cannot be dropped: there are two different simple games, neither of them weighted, with the same swing table. -/
theorem exists_not_weighted_simple_games_ne_of_swing_table_eq :
    ∃ f g : Finset (Fin 5) → Bool, is_simple_game f ∧ is_simple_game g ∧
      ¬ is_weighted_game f ∧ ¬ is_weighted_game g ∧
      (∀ i k, swing_table f i k = swing_table g i k) ∧ f ≠ g := by
  obtain ⟨f, g, hf, hg, h, hne⟩ := exists_simple_games_ne_of_swing_table_eq
  refine ⟨f, g, hf, hg, fun hw => hne (weighted_game_eq_of_swing_table_eq f g hf hw hg h),
    fun hw => hne (weighted_game_eq_of_swing_table_eq g f hg hw hf fun i k => (h i k).symm).symm, h, hne⟩
