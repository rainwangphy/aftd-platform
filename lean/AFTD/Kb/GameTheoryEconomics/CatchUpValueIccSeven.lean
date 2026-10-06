import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValue
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpValueIccEqEval

/-!
# catch_up_value_icc_seven

Topic: combinatorial_games   Node: fce9249bef23

Provenance: formalization of a published result. Source: Catch-Up: A Game in Which the Lead Alternates (Game & Puzzle Design 1(2), 2015), Sec. 3.1 and Table 2: optimal play on {1,...,N} was computed (minimax with alpha-beta pruning) to be a draw for every N <= 20 with even total; this is the case N = 7, re-checked by the Lean kernel

Catch-Up on {1, ..., 7} is a draw under optimal play (the case N = 7 of the Catch-Up conjecture), evaluated by the Lean kernel.
-/

/-- Catch-Up on {1,...,7} is a draw (kernel-checked). -/
theorem catch_up_value_icc_seven : catch_up_value (Finset.Icc 1 7) = CatchUpOutcome.draw := by
  rw [catch_up_value_icc_eq_eval]; decide +kernel
