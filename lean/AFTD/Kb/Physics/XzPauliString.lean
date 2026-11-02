import AFTD.Prelude
import AFTD.Kb.Physics.XzPauli
import AFTD.Kb.Tcs.PauliString

/-!
# xz_pauli_string

Topic: quantum_mechanics   Node: 611434f7805f

Provenance: formalization of a published result. Source: arXiv:2610.20846, Appendix C

The function `xz_pauli_string (L : ℕ) : (Fin L → Fin 2) → PauliString L` mapping a configuration a : Fin L → Fin 2 to the Pauli string whose value at site j : Fin L is `xz_pauli (a j) (a ⟨(j.val + 1) % L, _⟩)`.
-/

/-- The Pauli string on L qubits induced by a binary configuration with periodic boundary conditions. -/
def xz_pauli_string (L : ℕ) (a : Fin L → Fin 2) : PauliString L := fun j => xz_pauli (a j) (a ⟨(j.val + 1) % L, by
    rcases L with _ | L'
    · exact j.elim0
    · exact Nat.mod_lt _ (Nat.succ_pos L')⟩)
