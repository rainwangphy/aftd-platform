import AFTD.Prelude
import AFTD.Kb.Tcs.CliffordTGateMatrix
import AFTD.Kb.Tcs.CliffordTGate

/-!
# clifford_t_circuit_matrix

Topic: quantum   Node: ff44ed3292f2

The unitary of a Clifford+T circuit given as a list of gates, the first gate of the list acting first: g_k ... g_2 g_1.
-/

/-- The unitary of a circuit, its gates applied in list order (the first gate acts first). -/
noncomputable def clifford_t_circuit_matrix {N : ℕ} (gs : List (CliffordTGate N)) : Matrix (Fin N → Bool) (Fin N → Bool) ℂ :=
  gs.foldl (fun U g => clifford_t_gate_matrix g * U) 1
