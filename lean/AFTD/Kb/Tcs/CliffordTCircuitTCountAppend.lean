import AFTD.Prelude
import AFTD.Kb.Tcs.CliffordTCircuitTCount
import AFTD.Kb.Tcs.CliffordTGate
import AFTD.Kb.Tcs.CliffordTCircuitTCountNil

/-!
# clifford_t_circuit_t_count_append

Topic: quantum   Node: fa159391b47e

Provenance: helper lemma. step towards ccz_layer_t_count_below_6m_plus_1_with_hadamards

The T-count of the concatenation of two Clifford+T circuits is the sum of their T-counts.
-/

/-- The T-count of the concatenation of two Clifford+T circuits is the sum of their T-counts. -/
theorem clifford_t_circuit_t_count_append {N : ℕ} (gs1 gs2 : List (CliffordTGate N)) :
    clifford_t_circuit_t_count (gs1 ++ gs2) = clifford_t_circuit_t_count gs1 + clifford_t_circuit_t_count gs2 := by first | exact clifford_t_circuit_t_count_nil | (apply clifford_t_circuit_t_count_nil <;> assumption) | (apply clifford_t_circuit_t_count_nil <;> simp_all) | simpa using clifford_t_circuit_t_count_nil | (simp only [CliffordTGate, clifford_t_circuit_t_count] at *; first | exact clifford_t_circuit_t_count_nil | (apply clifford_t_circuit_t_count_nil <;> assumption) | (apply clifford_t_circuit_t_count_nil <;> simp_all) | simpa using clifford_t_circuit_t_count_nil)
