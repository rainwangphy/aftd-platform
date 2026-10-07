import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAuxEmpty
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome

/-!
# catch_up_value_aux_empty_eq_draw_iff

Topic: combinatorial_games   Node: 7c16aaef5176

Provenance: helper lemma. Catch-Up: A Game in Which the Lead Alternates (2015)

In a Catch-Up position with an empty set of remaining pieces, the game value for the mover is CatchUpOutcome.draw if and only if the mover's score equals the opponent's score.
-/

/-- When no pieces remain in Catch-Up, the position is a draw if and only if the player scores are equal. -/
theorem catch_up_value_aux_empty_eq_draw_iff (s_me s_opp : ℕ) (isFirstMove : Bool) :
    catch_up_value_aux ∅ s_me s_opp isFirstMove = CatchUpOutcome.draw ↔ s_me = s_opp := by
  rw [catch_up_value_aux_empty]
  split_ifs <;> simp <;> omega
