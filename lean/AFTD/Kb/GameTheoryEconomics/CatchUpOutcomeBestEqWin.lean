import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBest

/-!
# catch_up_outcome_best_eq_win

Topic: combinatorial_games   Node: a6cc42e3cec3

Under Catch-Up's best-outcome aggregation on a list of outcomes, the aggregated outcome is a win if and only if a win appears in the list.
-/

lemma catch_up_outcome_best_foldl_win_spec (f : CatchUpOutcome → CatchUpOutcome → CatchUpOutcome)
    (hf : ∀ a b, f a b = if a = .win ∨ b = .win then .win
      else if a = .draw ∨ b = .draw then .draw else .loss)
    (os : List CatchUpOutcome) (acc : CatchUpOutcome) :
    os.foldl f acc = CatchUpOutcome.win ↔ acc = CatchUpOutcome.win ∨ CatchUpOutcome.win ∈ os := by
  induction os generalizing acc with
  | nil => simp
  | cons head tail ih =>
    rw [List.foldl_cons, ih, hf, List.mem_cons]
    cases acc <;> cases head <;> simp

/-- The best outcome of a list of Catch-Up outcomes is a win if and only if a win is in the list. -/
theorem catch_up_outcome_best_eq_win (os : List CatchUpOutcome) :
    CatchUpOutcome.best os = CatchUpOutcome.win ↔ CatchUpOutcome.win ∈ os := by
  unfold CatchUpOutcome.best
  rw [catch_up_outcome_best_foldl_win_spec _ (by intro a b; cases a <;> cases b <;> rfl)]
  simp
