import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBest
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeNeg

/-!
# catch_up_value_aux_zero_zero

Topic: combinatorial_games   Node: 43dbc564028c

Provenance: helper lemma. step towards the Catch-Up conjecture (Catch-Up: A Game in Which the Lead Alternates (Game & Puzzle Design 1(2), 2015), Sec. 3.1; formal-conjectures CatchUpConjecture.lean) (Catch-Up ladder step)

For any nonempty set S of pieces, the auxiliary Catch-Up value from scores (0, 0) is the best outcome among all opening moves x ∈ S.
-/

/-- Unfolding catch_up_value_aux on a nonempty set from scores (0, 0) yields the best outcome of the negated positions after each opening choice. -/
theorem catch_up_value_aux_zero_zero (S : Finset ℕ) (hS : S.Nonempty) :
    catch_up_value_aux S 0 0 false =
      CatchUpOutcome.best (S.attach.toList.map (fun ⟨x, _⟩ =>
        (catch_up_value_aux (S.erase x) 0 x false).neg)) := by
  conv_lhs => rw [catch_up_value_aux]
  have hrem : S ≠ ∅ := Finset.Nonempty.ne_empty hS
  simp only [hrem, ite_false]
  have hnot_lt : ¬ (0 + ∑ x ∈ S, x < 0) := by omega
  simp only [hnot_lt, ite_false]
  apply congr_arg CatchUpOutcome.best
  apply List.map_congr_left
  intro ⟨x, hx⟩ hx_in
  dsimp
  rw [zero_add]
