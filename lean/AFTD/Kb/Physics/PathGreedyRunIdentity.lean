import AFTD.Prelude
import AFTD.Kb.Physics.PathGreedyRun
import AFTD.Kb.Physics.PathOddRunFinish

/-!
# pathGreedyRun_identity

Topic: quantum_mechanics   Node: 0f71d7191b32

Provenance: helper lemma. Finite-state path cut-matching certificate for OP-827; exhaustive transition check in experiment 22529.

The greedy matching count and pending run parity satisfy an exact counting identity.
-/

open scoped BigOperators in
theorem pathGreedyRun_identity (p : Bool) (xs : List Bool) :
    2 * pathGreedyRun p xs + (if p then 1 else 0) = xs.countP id + pathOddRunFinish p xs := by
  induction xs generalizing p with
  | nil => cases p <;> rfl
  | cons b bs ih =>
    cases p <;> cases b <;> simp [pathGreedyRun, pathOddRunFinish, List.countP_cons] at * <;> omega
