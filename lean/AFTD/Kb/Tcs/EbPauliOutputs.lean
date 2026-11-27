import AFTD.Prelude
import AFTD.Kb.Tcs.IsEbPauliChannel
import AFTD.Kb.Tcs.PauliChannelApply
import AFTD.Kb.Tcs.IsDensityMatrixState
import AFTD.Kb.Tcs.PauliString

/-!
# eb_pauli_outputs

Topic: quantum   Node: 565733c49959

Provenance: formalization of a published result. Source: arXiv:2611.34872, Conjecture 4

The set eb_pauli_outputs n is the set of all density matrices σ = pauli_channel_apply p ρ where p is an entanglement-breaking Pauli distribution on n qubits and ρ is an n-qubit density matrix state.
-/

/-- The set of all outputs of entanglement-breaking Pauli channels on n qubits. -/
def eb_pauli_outputs (n : ℕ) : Set (Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :=
  { σ | ∃ (p : PauliString n → ℝ) (ρ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ),
    is_eb_pauli_channel p ∧ is_density_matrix_state ρ ∧ σ = pauli_channel_apply p ρ }
