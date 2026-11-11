import AFTD.Prelude
import AFTD.Kb.Physics.PathGreedyRunIdentity
import AFTD.Kb.Physics.PathOddRunFinishIdentity
import AFTD.Kb.Physics.OddRunCount
import AFTD.Kb.Physics.PathGreedyRun
import AFTD.Kb.Physics.PathOddRunFinish
import AFTD.Kb.Physics.OddRunAux

/-!
# pathGreedyRun_eq_count_and_odd

Topic: quantum_mechanics   Node: 62beffaba4e4

Provenance: helper lemma. Finite-state path cut-matching certificate for OP-827; exhaustive transition check in experiment 22529.

Twice the greedy count equals the number of true edges plus the number of odd true runs.
-/

open scoped BigOperators in
theorem pathGreedyRun_eq_count_and_odd (xs : List Bool) :
    2 * pathGreedyRun false xs = xs.countP id + odd_run_count xs := by
  have h := pathGreedyRun_identity false xs
  have h2 := pathOddRunFinish_identity false false xs
  simp only [Bool.false_and] at h h2
  change odd_run_count xs = pathOddRunFinish false xs at h2
  simpa [h2] using h
