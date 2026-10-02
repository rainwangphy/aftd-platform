import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux

/-!
# catch_up_value_aux_loss_of_sum_lt

Topic: combinatorial_games   Node: 6269bf028a42

In a Catch-Up position, if the mover's score plus the sum of all remaining numbers is strictly less than the opponent's score, then the game value for the mover is a loss, regardless of the remaining set or the isFirstMove flag.
-/

/-- In Catch-Up, if the mover's current score plus the sum of all remaining pieces is strictly less than the opponent's score, the mover loses. -/
theorem catch_up_value_aux_loss_of_sum_lt (remaining : Finset ℕ) (s_me s_opp : ℕ) (isFirstMove : Bool)
    (h : s_me + remaining.sum (fun x => x) < s_opp) :
    catch_up_value_aux remaining s_me s_opp isFirstMove = CatchUpOutcome.loss := by
  rw [catch_up_value_aux.eq_def]
  by_cases hr : remaining = ∅
  · subst hr
    simp only [Finset.sum_empty, add_zero] at h
    have h1 : ¬ (s_opp < s_me) := by omega
    simp [h1, h]
  · simp [hr, h]
