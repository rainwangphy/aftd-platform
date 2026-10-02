import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBest

/-!
# catch_up_value_aux_add_scores

Topic: combinatorial_games   Node: f16eb038974d

In Catch-Up, adding a constant c to both the mover's and the opponent's score leaves the game value unchanged, because only score comparisons and differences govern the game.
-/

/-- In Catch-Up, adding the same constant c to both players' scores preserves the game value from any position. -/
theorem catch_up_value_aux_add_scores (remaining : Finset ℕ) (s_me s_opp c : ℕ) (isFirstMove : Bool) :
    catch_up_value_aux remaining (s_me + c) (s_opp + c) isFirstMove =
      catch_up_value_aux remaining s_me s_opp isFirstMove := by
  conv_lhs => rw [catch_up_value_aux]
  conv_rhs => rw [catch_up_value_aux]
  by_cases hrem : remaining = ∅
  · simp only [hrem, ite_true]
    have hgt : (s_me + c > s_opp + c) ↔ (s_me > s_opp) := by omega
    have hlt : (s_opp + c > s_me + c) ↔ (s_opp > s_me) := by omega
    simp only [hgt, hlt]
  · simp only [hrem, ite_false]
    have hsum : (s_me + c + ∑ x ∈ remaining, x < s_opp + c) ↔ (s_me + ∑ x ∈ remaining, x < s_opp) := by omega
    simp only [hsum]
    by_cases hloss : s_me + ∑ x ∈ remaining, x < s_opp
    · simp only [hloss, ite_true]
    · simp only [hloss, ite_false]
      apply congr_arg CatchUpOutcome.best
      apply List.map_congr_left
      intro ⟨x, hx⟩ hx_in
      dsimp
      have h1 : s_me + c + x = (s_me + x) + c := by omega
      have hge : (s_me + c + x ≥ s_opp + c) ↔ (s_me + x ≥ s_opp) := by omega
      simp only [hge]
      cases isFirstMove
      · simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases hge_case : s_me + x ≥ s_opp
        · simp only [hge_case, ite_true]
          congr 1
          rw [h1]
          exact catch_up_value_aux_add_scores (remaining.erase x) s_opp (s_me + x) c false
        · simp only [hge_case, ite_false]
          rw [h1]
          exact catch_up_value_aux_add_scores (remaining.erase x) (s_me + x) s_opp c false
      · simp only [↓reduceIte]
        congr 1
        rw [h1]
        exact catch_up_value_aux_add_scores (remaining.erase x) s_opp (s_me + x) c false
termination_by remaining.card
decreasing_by
  all_goals
    simpa using Finset.card_erase_lt_of_mem hx
