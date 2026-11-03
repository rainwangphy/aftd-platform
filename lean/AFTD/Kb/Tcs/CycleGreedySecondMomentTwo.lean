import AFTD.Prelude
import AFTD.Kb.Tcs.CycleGreedySecondMoment
import AFTD.Kb.Tcs.CycleGreedySecondMomentFormula
import AFTD.Kb.Tcs.CycleGreedyMomentsFuel
import AFTD.Kb.Tcs.CycleGreedyMoments
import AFTD.Kb.Tcs.CycleGapMerge
import AFTD.Kb.Tcs.CycleGreedyS

/-!
# cycle_greedy_second_moment_two

Topic: online_algorithms   Node: 95f04c53b099

Provenance: formalization of a published result. Source: OP-890

For n = 2, the exact rational second moment equals the conjectured formula value: `cycle_greedy_second_moment 2 = cycle_greedy_second_moment_formula 2`.
-/

/-- For n = 2, the exact second moment equals the conjectured formula value. -/
theorem cycle_greedy_second_moment_two :
    cycle_greedy_second_moment 2 = cycle_greedy_second_moment_formula 2 := by
  have h1 : cycle_greedy_second_moment 2 = 2/3 := by
    unfold cycle_greedy_second_moment cycle_greedy_moments
    simp only [List.length_replicate]
    simp only [cycle_greedy_moments_fuel.eq_def]
    simp only [cycle_gap_merge, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil, List.replicate_succ, List.replicate_zero, List.length_cons, List.length_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.head?_cons, List.getLast?_cons]
    norm_num
  have h2 : cycle_greedy_second_moment_formula 2 = 2/3 := by
    simp [cycle_greedy_second_moment_formula, cycle_greedy_s, Finset.sum_range_succ]
    norm_num
  rw [h1, h2]
