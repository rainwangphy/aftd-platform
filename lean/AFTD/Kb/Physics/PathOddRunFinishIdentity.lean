import AFTD.Prelude
import AFTD.Kb.Physics.OddRunAux
import AFTD.Kb.Physics.PathOddRunFinish

/-!
# pathOddRunFinish_identity

Topic: quantum_mechanics   Node: 3f7a887669c1

Provenance: helper lemma. Finite-state path cut-matching certificate for OP-827; exhaustive transition check in experiment 22529.

The pending parity counter agrees with the existing odd-run counter.
-/

open scoped BigOperators in
theorem pathOddRunFinish_identity (ir odd : Bool) (xs : List Bool) :
    odd_run_aux ir odd (xs ++ [false]) = pathOddRunFinish (ir && odd) xs := by
  induction xs generalizing ir odd with
  | nil => cases ir <;> cases odd <;> rfl
  | cons b bs ih =>
    cases ir <;> cases odd <;> cases b <;> simp [odd_run_aux, pathOddRunFinish, ih]
