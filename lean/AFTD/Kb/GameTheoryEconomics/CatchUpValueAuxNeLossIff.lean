import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBestEqLoss
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeNeg

/-!
# catch_up_value_aux_ne_loss_iff

Topic: combinatorial_games   Node: dcbfe197ed7f

In Catch-Up with nonempty remaining pieces and score plus remaining sum at least opponent's score, the mover does not lose if and only if there exists a move y such that the resulting position is not a win for opponent (if turn passes) or not a loss for mover (if turn continues).
-/

/-- In a Catch-Up position where remaining pieces are nonempty and the mover is not deficit-dominated, the outcome is not a loss if and only if there exists a valid move leading to a non-losing position. -/
theorem catch_up_value_aux_ne_loss_iff (remaining : Finset ℕ) (s_me s_opp : ℕ)
    (hrem : remaining.Nonempty) (hsum : ¬ s_me + ∑ x ∈ remaining, x < s_opp) :
    catch_up_value_aux remaining s_me s_opp false ≠ CatchUpOutcome.loss ↔
      ∃ y ∈ remaining,
        if s_me + y ≥ s_opp then
          catch_up_value_aux (remaining.erase y) s_opp (s_me + y) false ≠ CatchUpOutcome.win
        else
          catch_up_value_aux (remaining.erase y) (s_me + y) s_opp false ≠ CatchUpOutcome.loss := by
  conv_lhs => rw [catch_up_value_aux]
  have hne : remaining ≠ ∅ := Finset.Nonempty.ne_empty hrem
  simp only [hne, ite_false, hsum]
  dsimp
  rw [catch_up_outcome_best_eq_loss]
  have h_neg (o : CatchUpOutcome) : o.neg = CatchUpOutcome.loss ↔ o = CatchUpOutcome.win := by
    cases o <;> decide
  simp [apply_ite (fun x => ¬ x = CatchUpOutcome.loss), h_neg]
