import AFTD.Prelude
import AFTD.Kb.Tcs.ApplyCliffordGate
import AFTD.Kb.Tcs.PauliSize
import AFTD.Kb.Tcs.CliffordGate
import AFTD.Kb.Tcs.PauliLabel

/-!
# pauli_size_apply_clifford_gate_s

Topic: quantum   Node: b823329e29b0

Provenance: helper lemma. step towards op_757_all_to_all_cnot_lower_bound

Single-qubit Phase gate preserves the Pauli size of any Pauli label.
-/

/-- Single-qubit Phase gate preserves the Pauli size of any Pauli label. -/
theorem pauli_size_apply_clifford_gate_s {k : ℕ} (i : Fin k) (p : PauliLabel k) :
    pauli_size (apply_clifford_gate (.s i) p) = pauli_size p := by
  -- The phase gate acts as (a, b) ↦ (a, b + a) on the qubit i; elsewhere nothing changes.
  have hp : apply_clifford_gate (CliffordGate.s i) p
      = (p.1, Function.update p.2 i (p.2 i + p.1 i)) := rfl
  rw [hp]
  -- The support predicate agrees pointwise with that of p.
  have h : (Finset.univ.filter fun j : Fin k =>
        p.1 j ≠ 0 ∨ Function.update p.2 i (p.2 i + p.1 i) j ≠ 0)
      = (Finset.univ.filter fun j : Fin k => p.1 j ≠ 0 ∨ p.2 j ≠ 0) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hj : j = i
    · -- On qubit i, `a ≠ 0 ∨ b + a ≠ 0 ↔ a ≠ 0 ∨ b ≠ 0` in ZMod 2.
      rw [hj, Function.update_self]
      by_cases ha : p.1 i = 0 <;> simp [ha]
    · rw [Function.update_of_ne hj]
  rw [pauli_size, pauli_size, h]
