import AFTD.Prelude
import AFTD.Kb.Tcs.BackIdentityMatrix
import AFTD.Kb.Tcs.GoethalsSeidelArray

/-!
# bordered_goethals_seidel_matrix

Topic: combinatorics   Node: a10987243692

Provenance: formalization of a published result. Source: arXiv:2610.27175 (Recent progress in the construction of Hadamard matrices), Theorem 5 (the bordered array)

The (4m+4) × (4m+4) matrix of arXiv:2610.27175 Theorem 5, indexed by Fin 4 ⊕ (Fin 4 × Fin m): top-left 4 × 4 block with diagonal 1 and off-diagonal -1; top border rows (j, j, j, j), (j, -j, j, -j), (j, -j, -j, j), (j, j, -j, -j); left border columns with signs (1,1,1,1), (-1,1,1,-1), (-1,-1,1,1), (-1,1,-1,1); bottom-right the Goethals-Seidel array in A, B, C, D and the back-identity R.
-/

/-- The (4m+4) × (4m+4) matrix of arXiv:2610.27175 Theorem 5, indexed by Fin 4 ⊕ (Fin 4 × Fin m): top-left 4 × 4 block with diagonal 1 and off-diagonal -1; top border rows (j, j, j, j), (j, -j, j, -j), (j, -j, -j, j), (j, j, -j, -j); left border columns with signs (1,1,1,1), (-1,1,1,-1), (-1,-1,1,1), (-1,1,-1,1); bottom-right the Goethals-Seidel array in A, B, C, D and the back-identity R. -/
def bordered_goethals_seidel_matrix {m : ℕ} (A B C D : Matrix (Fin m) (Fin m) ℤ) :
    Matrix (Fin 4 ⊕ Fin 4 × Fin m) (Fin 4 ⊕ Fin 4 × Fin m) ℤ :=
  Matrix.fromBlocks
    (!![1, -1, -1, -1; -1, 1, -1, -1; -1, -1, 1, -1; -1, -1, -1, 1])
    (Matrix.of fun r q =>
      !![1, 1, 1, 1; 1, -1, 1, -1; 1, -1, -1, 1; 1, 1, -1, -1] r q.1)
    (Matrix.of fun p c =>
      !![1, 1, 1, 1; -1, 1, 1, -1; -1, -1, 1, 1; -1, 1, -1, 1] p.1 c)
    (goethals_seidel_array A B C D (back_identity_matrix m))
