import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValue
import AFTD.Kb.GameTheoryEconomics.CatchUpValueIccEqDrawOfSearch

/-!
# catch_up_value_icc_eleven

Topic: combinatorial_games   Node: 6acb726788b2

Provenance: formalization of a published result. Source: Catch-Up: A Game in Which the Lead Alternates (Game & Puzzle Design 1(2), 2015), Sec. 3.1 and Table 2: optimal play on {1,...,N} was computed (minimax with alpha-beta pruning) to be a draw for every N <= 20 with even total; this is the case N = 11, re-checked by the Lean kernel

Catch-Up on {1, ..., 11} is a draw under optimal play (the case N = 11 of the Catch-Up conjecture), established by the kernel through the pruned search.
-/

/-- Catch-Up on {1,...,11} is a draw (kernel-checked). -/
theorem catch_up_value_icc_eleven : catch_up_value (Finset.Icc 1 11) = .draw :=
  catch_up_value_icc_eq_draw_of_search 11 (by decide +kernel) (by decide +kernel)
