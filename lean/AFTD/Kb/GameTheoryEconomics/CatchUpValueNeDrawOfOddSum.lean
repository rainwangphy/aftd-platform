import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValue
import AFTD.Kb.GameTheoryEconomics.CatchUpValueEqAuxFalse
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAuxNeDrawOfOddSum
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome

/-!
# catch_up_value_ne_draw_of_odd_sum

Topic: combinatorial_games   Node: 757618379ecb

For any finite set S of natural numbers whose sum is odd, the game value catch_up_value S is not a draw.
-/

/-- Catch-Up played on a finite set S of pieces whose total sum is odd cannot end in a draw. -/
theorem catch_up_value_ne_draw_of_odd_sum (S : Finset ℕ) (h_odd : Odd (S.sum (fun x => x))) :
    catch_up_value S ≠ CatchUpOutcome.draw := by
  rw [catch_up_value_eq_aux_false]
  apply catch_up_value_aux_ne_draw_of_odd_sum
  simpa using h_odd
