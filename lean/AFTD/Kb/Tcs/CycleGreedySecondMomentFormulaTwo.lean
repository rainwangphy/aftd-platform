import AFTD.Prelude
import AFTD.Kb.Tcs.CycleGreedySecondMomentFormula
import AFTD.Kb.Tcs.CycleGreedySTwo
import AFTD.Kb.Tcs.CycleGreedyS

/-!
# cycle_greedy_second_moment_formula_two

Topic: online_algorithms   Node: d11356df7bde

Provenance: helper lemma. OP-890

The closed-form second moment formula evaluates to 2/3 at n = 2: `cycle_greedy_second_moment_formula 2 = 2 / 3`.
-/

/-- Evaluation of the closed second moment formula at n = 2 gives 2/3. -/
theorem cycle_greedy_second_moment_formula_two : cycle_greedy_second_moment_formula 2 = 2 / 3 := by
  unfold cycle_greedy_second_moment_formula
  rw [cycle_greedy_s_two]
  norm_num
