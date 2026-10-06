import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBest

/-!
# catch_up_outcome_best_eq_draw

Topic: combinatorial_games   Node: f037d33980e1

Provenance: helper lemma. step towards the Catch-Up conjecture (Catch-Up: A Game in Which the Lead Alternates (Game & Puzzle Design 1(2), 2015), Sec. 3.1; formal-conjectures CatchUpConjecture.lean) (Catch-Up ladder step)

Under Catch-Up's best-outcome aggregation on a list of outcomes, the aggregated outcome is a draw if and only if no win appears in the list and at least one draw appears.
-/

lemma catch_up_outcome_best_foldl_draw_spec (f : CatchUpOutcome → CatchUpOutcome → CatchUpOutcome)
    (hf : ∀ a b, f a b = if a = .win ∨ b = .win then .win
      else if a = .draw ∨ b = .draw then .draw else .loss)
    (os : List CatchUpOutcome) (acc : CatchUpOutcome) :
    os.foldl f acc = CatchUpOutcome.draw ↔
      CatchUpOutcome.win ∉ os ∧
        (acc = CatchUpOutcome.draw ∨ (acc = CatchUpOutcome.loss ∧ CatchUpOutcome.draw ∈ os)) := by
  induction os generalizing acc with
  | nil => simp
  | cons head tail ih =>
    rw [List.foldl_cons, ih, hf, List.mem_cons, List.mem_cons]
    cases acc <;> cases head <;> simp

/-- Under Catch-Up's best-outcome aggregation on a list of outcomes, the outcome is a draw iff no win appears and at least one draw appears. -/
theorem catch_up_outcome_best_eq_draw (os : List CatchUpOutcome) :
    CatchUpOutcome.best os = CatchUpOutcome.draw ↔
      CatchUpOutcome.win ∉ os ∧ CatchUpOutcome.draw ∈ os := by
  unfold CatchUpOutcome.best
  rw [catch_up_outcome_best_foldl_draw_spec _ (by intro a b; cases a <;> cases b <;> rfl)]
  simp
