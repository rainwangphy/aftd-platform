import AFTD.Prelude
import AFTD.Kb.Physics.XzPauli
import AFTD.Kb.Tcs.PauliBasisToMatrix

/-!
# xz_transfer_matrix

Topic: quantum_mechanics   Node: 067a72a9a6ed

Provenance: helper lemma. step towards xz_scar_purity_doubling_of_odd_length

The 16x16 transfer matrix M whose entries M u v are given by the trace of the 4-fold product of Pauli matrices (xz_pauli (u 0) (v 0)).toMatrix * (xz_pauli (u 1) (v 1)).toMatrix * (xz_pauli (u 2) (v 2)).toMatrix * (xz_pauli (u 3) (v 3)).toMatrix.
-/

/-- The 16x16 transfer matrix for the XZ scar model, whose entries are the traces of 4-fold Pauli products. -/
noncomputable def xz_transfer_matrix : Matrix (Fin 4 → Fin 2) (Fin 4 → Fin 2) ℂ := fun u v => Matrix.trace (
  (xz_pauli (u 0) (v 0)).toMatrix *
  (xz_pauli (u 1) (v 1)).toMatrix *
  (xz_pauli (u 2) (v 2)).toMatrix *
  (xz_pauli (u 3) (v 3)).toMatrix)
