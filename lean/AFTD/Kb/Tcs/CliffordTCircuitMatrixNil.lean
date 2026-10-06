import AFTD.Prelude
import AFTD.Kb.Tcs.CliffordTCircuitMatrix
import AFTD.Kb.Tcs.CliffordTGate

/-!
# clifford_t_circuit_matrix_nil

Topic: quantum   Node: 1437c723400f

Provenance: original.

Sanity check: the empty circuit has the identity matrix.
-/

theorem clifford_t_circuit_matrix_nil (N : ℕ) : clifford_t_circuit_matrix ([] : List (CliffordTGate N)) = 1 := rfl
