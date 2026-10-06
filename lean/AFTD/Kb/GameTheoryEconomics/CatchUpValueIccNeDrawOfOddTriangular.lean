import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueNeDrawOfOddSum
import AFTD.Kb.GameTheoryEconomics.CatchUpSumIccId
import AFTD.Kb.GameTheoryEconomics.CatchUpValue
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome

/-!
# catch_up_value_icc_ne_draw_of_odd_triangular

Topic: combinatorial_games   Node: 53328de102bf

Provenance: formalization of a published result. Source: Catch-Up: A Game in Which the Lead Alternates (Game & Puzzle Design 1(2), 2015), Sec. 2.6 and Appendix 5.1 (an odd total cannot be split evenly, so no draw)

For any natural number N such that N(N+1)/2 is odd, catch_up_value (Finset.Icc 1 N) ≠ CatchUpOutcome.draw.
-/

/-- The converse half of the Catch-Up characterisation: if the triangular number N(N+1)/2 is odd, Catch-Up on {1, ..., N} cannot end in a draw. -/
theorem catch_up_value_icc_ne_draw_of_odd_triangular (N : ℕ) (h_odd : Odd (N * (N + 1) / 2)) :
    catch_up_value (Finset.Icc 1 N) ≠ CatchUpOutcome.draw := by
  apply catch_up_value_ne_draw_of_odd_sum
  rw [catch_up_sum_icc_id]
  exact h_odd
