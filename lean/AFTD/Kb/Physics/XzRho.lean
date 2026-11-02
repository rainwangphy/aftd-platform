import AFTD.Prelude
import AFTD.Kb.Physics.XzMatrixA

/-!
# xz_rho

Topic: quantum_mechanics   Node: eecfbf26a19b

Provenance: formalization of a published result. Source: arXiv:2610.20846, Appendix C

The reduced density matrix `xz_rho (L : ℕ) : Matrix (Fin L → Fin 2) (Fin L → Fin 2) ℂ` defined as the matrix square `(xz_matrix_a L) * (xz_matrix_a L)`.
-/

/-- The reduced density matrix rho_L = A_L^2 on L qubits. -/
noncomputable def xz_rho (L : ℕ) : Matrix (Fin L → Fin 2) (Fin L → Fin 2) ℂ := (xz_matrix_a L) * (xz_matrix_a L)
