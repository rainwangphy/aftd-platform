import AFTD.Prelude
import AFTD.Kb.Tcs.CycleGreedySecondMoment
import AFTD.Kb.Tcs.CycleGreedySecondMomentFormula
import AFTD.Kb.Tcs.CycleGreedyMomentsFuel
import AFTD.Kb.Tcs.CycleGreedyMoments
import AFTD.Kb.Tcs.CycleGapMerge
import AFTD.Kb.Tcs.CycleGreedyS

/-!
# cycle_greedy_second_moment_three

Topic: online_algorithms   Node: b3a561c0f733

Provenance: formalization of a published result. Source: OP-890

For n = 3, the exact rational second moment equals the conjectured formula value: `cycle_greedy_second_moment 3 = cycle_greedy_second_moment_formula 3`.
-/

/-- For n = 3, the exact second moment equals the conjectured formula value. -/
theorem cycle_greedy_second_moment_three :
    cycle_greedy_second_moment 3 = cycle_greedy_second_moment_formula 3 := by
  have h1 : cycle_greedy_second_moment 3 = 55/24 := by
    unfold cycle_greedy_second_moment cycle_greedy_moments
    simp only [List.length_replicate]
    simp [cycle_greedy_moments_fuel.eq_def, cycle_gap_merge,
      show List.range 3 = [0,1,2] from rfl, show List.range 2 = [0,1] from rfl]
    norm_num
  have h2 : cycle_greedy_second_moment_formula 3 = 55/24 := by
    simp [cycle_greedy_second_moment_formula, cycle_greedy_s, Finset.sum_range_succ,
      Finset.prod_Icc_succ_top]
    norm_num
  rw [h1, h2]
