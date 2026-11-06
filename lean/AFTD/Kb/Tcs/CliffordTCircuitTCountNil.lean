import AFTD.Prelude
import AFTD.Kb.Tcs.CliffordTCircuitTCount
import AFTD.Kb.Tcs.CliffordTGate
import AFTD.Kb.Tcs.CliffordTCircuitTCountExample

/-!
# clifford_t_circuit_t_count_nil

Topic: quantum   Node: 1f0fa96af5e9

Provenance: helper lemma. step towards ccz_layer_t_count_below_6m_plus_1_with_hadamards

The empty Clifford+T circuit has T-count 0.
-/

/-- The empty Clifford+T circuit has T-count 0. -/
theorem clifford_t_circuit_t_count_nil {N : ℕ} :
    clifford_t_circuit_t_count ([] : List (CliffordTGate N)) = 0 := by first | exact clifford_t_circuit_t_count_example | (apply clifford_t_circuit_t_count_example <;> assumption) | (apply clifford_t_circuit_t_count_example <;> simp_all) | simpa using clifford_t_circuit_t_count_example | (simp only [CliffordTGate, clifford_t_circuit_t_count] at *; first | exact clifford_t_circuit_t_count_example | (apply clifford_t_circuit_t_count_example <;> assumption) | (apply clifford_t_circuit_t_count_example <;> simp_all) | simpa using clifford_t_circuit_t_count_example)
