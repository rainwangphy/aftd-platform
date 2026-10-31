import AFTD.Prelude
import AFTD.Kb.Tcs.CliffordGate
import AFTD.Kb.Tcs.CliffordCircuitScore

/-!
# clifford_circuit_score_one_nil

Topic: quantum   Node: 3bd937285599

Provenance: helper lemma. scout/2610-04621-exact-clifford-optimality-for-two-sided-locally-randomized.md:370

Sanity check: the empty Clifford circuit on 1 qubit has score 3.
-/

/-- Sanity check: the empty Clifford circuit on 1 qubit has score 3. -/
theorem clifford_circuit_score_one_nil : clifford_circuit_score ([] : List (CliffordGate 1)) = 3 := by
  decide
