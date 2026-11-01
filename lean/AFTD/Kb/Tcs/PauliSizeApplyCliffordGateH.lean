import AFTD.Prelude
import AFTD.Kb.Tcs.PauliLabel
import AFTD.Kb.Tcs.PauliSize
import AFTD.Kb.Tcs.ApplyCliffordGate
import AFTD.Kb.Tcs.CliffordGate

/-!
# pauli_size_apply_clifford_gate_h

Topic: quantum   Node: a7af02b571d4

Provenance: helper lemma. step towards op_757_all_to_all_cnot_lower_bound

Single-qubit Hadamard gate preserves the Pauli size of any Pauli label.
-/

/-- Single-qubit Hadamard gate preserves the Pauli size of any Pauli label. -/
theorem pauli_size_apply_clifford_gate_h {k : ℕ} (i : Fin k) (p : PauliLabel k) :
    pauli_size (apply_clifford_gate (.h i) p) = pauli_size p := by
  unfold pauli_size apply_clifford_gate
  congr 1
  apply Finset.filter_congr
  intro j _
  by_cases hji : j = i
  · subst hji
    simp [Function.update_self, or_comm]
  · simp [Function.update_of_ne hji]
