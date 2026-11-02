import AFTD.Prelude
import AFTD.Kb.Physics.XzPauliString
import AFTD.Kb.Tcs.PauliMatrix

/-!
# xz_matrix_a

Topic: quantum_mechanics   Node: 29bbf421c76a

Provenance: formalization of a published result. Source: arXiv:2610.20846, Appendix C

The matrix `xz_matrix_a (L : ℕ) : Matrix (Fin L → Fin 2) (Fin L → Fin 2) ℂ` defined as `((1 : ℂ) / (2 ^ L : ℂ)) • ∑ a : Fin L → Fin 2, pauliMatrix (xz_pauli_string L a)`.
-/

/-- The normalized Hamiltonian/operator sum A_L on L qubits. -/
noncomputable def xz_matrix_a (L : ℕ) : Matrix (Fin L → Fin 2) (Fin L → Fin 2) ℂ := ((1 : ℂ) / (2 ^ L : ℂ)) • ∑ a : Fin L → Fin 2, pauliMatrix (xz_pauli_string L a)
