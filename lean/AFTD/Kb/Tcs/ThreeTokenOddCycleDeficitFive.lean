import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeTokenOddCycleDeficit
import AFTD.Kb.Tcs.WeightedMaxCutLinearCombination

/-!
# three_token_odd_cycle_deficit_five

Topic: graphs   Node: 1ea9a815407d

Provenance: helper lemma. arXiv:2611.22830 "Independent sets in the 2-token graph of a cycle and kings on the torus"; OP-2010

The value of three_token_odd_cycle_deficit at 5 equals 2.
-/

/-- Sanity check: the deficit at n = 5 is 2. -/
theorem three_token_odd_cycle_deficit_five : three_token_odd_cycle_deficit 5 = 2 := by first | exact weighted_max_cut_linear_combination | (apply weighted_max_cut_linear_combination <;> assumption) | (apply weighted_max_cut_linear_combination <;> simp_all) | simpa using weighted_max_cut_linear_combination | (simp only [three_token_odd_cycle_deficit] at *; first | exact weighted_max_cut_linear_combination | (apply weighted_max_cut_linear_combination <;> assumption) | (apply weighted_max_cut_linear_combination <;> simp_all) | simpa using weighted_max_cut_linear_combination)
