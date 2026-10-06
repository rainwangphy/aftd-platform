import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBest

/-!
# catch_up_value_aux_first_move_eq_of_eq_scores

Topic: combinatorial_games   Node: 203745db447b

Provenance: helper lemma. step towards the Catch-Up conjecture (Catch-Up: A Game in Which the Lead Alternates (Game & Puzzle Design 1(2), 2015), Sec. 3.1; formal-conjectures CatchUpConjecture.lean) (Catch-Up ladder step)

In a Catch-Up position where player scores are equal, every pick ends the mover's turn, so the game value with isFirstMove = true equals that with isFirstMove = false.
-/

/-- When the mover and opponent have equal scores in Catch-Up, every piece chosen keeps or exceeds the opponent score, so the opening flag is irrelevant. -/
theorem catch_up_value_aux_first_move_eq_of_eq_scores (remaining : Finset ℕ) (s : ℕ) :
    catch_up_value_aux remaining s s true = catch_up_value_aux remaining s s false := by
  conv_lhs => rw [catch_up_value_aux]
  conv_rhs => rw [catch_up_value_aux]
  by_cases hrem : remaining = ∅
  · simp [hrem]
  · simp only [hrem, ite_false]
    have hnot_lt : ¬ (s + ∑ x ∈ remaining, x < s) := by omega
    simp only [hnot_lt, ite_false]
    apply congr_arg CatchUpOutcome.best
    apply List.map_congr_left
    intro ⟨x, hx⟩ hx_in
    dsimp
    have hge : s + x ≥ s := by omega
    simp [hge]
