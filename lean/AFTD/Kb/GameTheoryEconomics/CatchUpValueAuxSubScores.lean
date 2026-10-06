import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAuxAddScores
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux

/-!
# catch_up_value_aux_sub_scores

Topic: combinatorial_games   Node: ac32ac568a8c

Provenance: helper lemma. step towards the Catch-Up conjecture (Catch-Up: A Game in Which the Lead Alternates (Game & Puzzle Design 1(2), 2015), Sec. 3.1; formal-conjectures CatchUpConjecture.lean) (Catch-Up ladder step)

In Catch-Up, when the mover's score s_me is at most the opponent's score s_opp, the game value equals that from scores 0 and s_opp - s_me.
-/

/-- In Catch-Up, when the mover's score is at most the opponent's score, the game value depends only on the score difference (the deficit). -/
theorem catch_up_value_aux_sub_scores (remaining : Finset ℕ) (s_me s_opp : ℕ) (hle : s_me ≤ s_opp) (isFirstMove : Bool) :
    catch_up_value_aux remaining s_me s_opp isFirstMove =
      catch_up_value_aux remaining 0 (s_opp - s_me) isFirstMove := by
  have h := catch_up_value_aux_add_scores remaining 0 (s_opp - s_me) s_me isFirstMove
  rw [zero_add, Nat.sub_add_cancel hle] at h
  exact h
