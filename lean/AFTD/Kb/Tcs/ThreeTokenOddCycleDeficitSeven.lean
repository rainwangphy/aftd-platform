import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeTokenOddCycleDeficit
import AFTD.Kb.Tcs.ThreeTokenOddCycleDeficitFive

/-!
# three_token_odd_cycle_deficit_seven

Topic: graphs   Node: 7863cb20413d

Provenance: helper lemma. arXiv:2611.22830 "Independent sets in the 2-token graph of a cycle and kings on the torus"; OP-2010

The value of three_token_odd_cycle_deficit at 7 equals 5.
-/

/-- Sanity check: the deficit at n = 7 is 5. -/
theorem three_token_odd_cycle_deficit_seven : three_token_odd_cycle_deficit 7 = 5 := by first | exact three_token_odd_cycle_deficit_five | (apply three_token_odd_cycle_deficit_five <;> assumption) | (apply three_token_odd_cycle_deficit_five <;> simp_all) | simpa using three_token_odd_cycle_deficit_five | (simp only [three_token_odd_cycle_deficit] at *; first | exact three_token_odd_cycle_deficit_five | (apply three_token_odd_cycle_deficit_five <;> assumption) | (apply three_token_odd_cycle_deficit_five <;> simp_all) | simpa using three_token_odd_cycle_deficit_five)
