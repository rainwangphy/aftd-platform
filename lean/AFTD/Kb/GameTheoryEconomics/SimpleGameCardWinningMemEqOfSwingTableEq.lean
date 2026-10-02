import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsSimpleGame
import AFTD.Kb.GameTheoryEconomics.SwingTable
import AFTD.Kb.GameTheoryEconomics.SimpleGameCardWinningEqOfSwingTableEq
import AFTD.Kb.GameTheoryEconomics.SumRangeSwingTableEq

/-!
# simple_game_card_winning_mem_eq_of_swing_table_eq

Topic: general_equilibrium   Node: b0975d67ef68

If two simple games have the same swing table, then for every player i they have the same number of winning coalitions containing i.
-/

/-- Two simple games with the same swing table have, for every player `i`, the same number of winning coalitions containing `i`. -/
theorem simple_game_card_winning_mem_eq_of_swing_table_eq {n : ℕ} (f g : Finset (Fin n) → Bool)
    (hf : is_simple_game f) (hg : is_simple_game g)
    (h : ∀ i k, swing_table f i k = swing_table g i k) (i : Fin n) :
    (Finset.univ.filter fun S : Finset (Fin n) => i ∈ S ∧ f S = true).card
      = (Finset.univ.filter fun S : Finset (Fin n) => i ∈ S ∧ g S = true).card := by
  have hs : ∑ k ∈ Finset.range (n + 1), (swing_table f i k : ℝ)
      = ∑ k ∈ Finset.range (n + 1), (swing_table g i k : ℝ) := by simp [h]
  rw [sum_range_swing_table_eq f hf.1 i, sum_range_swing_table_eq g hg.1 i,
    simple_game_card_winning_eq_of_swing_table_eq f g hf hg h] at hs
  exact_mod_cast (by linarith : ((Finset.univ.filter fun S : Finset (Fin n) => i ∈ S ∧ f S = true).card : ℝ)
      = (Finset.univ.filter fun S : Finset (Fin n) => i ∈ S ∧ g S = true).card)
