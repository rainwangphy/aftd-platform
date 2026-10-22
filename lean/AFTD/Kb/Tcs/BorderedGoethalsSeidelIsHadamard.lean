import AFTD.Prelude
import AFTD.Kb.Tcs.IsHadamardMatrix
import AFTD.Kb.Tcs.BorderedGoethalsSeidelMatrix
import AFTD.Kb.Tcs.BorderedGoethalsSeidelMatrixEntries
import AFTD.Kb.Tcs.BorderedGoethalsSeidelCornerBlock
import AFTD.Kb.Tcs.BorderedGoethalsSeidelCrossBlock
import AFTD.Kb.Tcs.BorderedGoethalsSeidelLowerBlock
import AFTD.Kb.Tcs.BackIdentityMatrix
import AFTD.Kb.Tcs.GoethalsSeidelArray

/-!
# bordered_goethals_seidel_is_hadamard

Topic: combinatorics   Node: cb7bea8d216d

Provenance: formalization of a published result. Source: arXiv:2610.27175 (Recent progress in the construction of Hadamard matrices), Theorem 5. Circulants are Mathlib's `Matrix.circulant` (entry (i, j) = v(i - j)); the paper's convention (first row) gives the same set of matrices. The matrix is indexed by Fin 4 ⊕ (Fin 4 × Fin m), of size 4m + 4.

Let m be even and let A, B, C, D be circulant {±1}-matrices of order m (first columns a, b, c, d) with AAᵀ + BBᵀ + CCᵀ + DDᵀ = (4m+4)I - 4J, A of row sum 2 and B, C, D of row sum 0. Then the bordered Goethals-Seidel matrix of order 4m+4 (corner 4 × 4 block with diagonal 1, off-diagonal -1; borders of ±j; Goethals-Seidel array in A, BR, CR, DR with R the back-identity) is a Hadamard matrix.
-/

theorem bordered_goethals_seidel_is_hadamard (m : ℕ) (hm : Even m) (a b c d : Fin m → ℤ)
    (ha : ∀ i, a i = 1 ∨ a i = -1) (hb : ∀ i, b i = 1 ∨ b i = -1)
    (hc : ∀ i, c i = 1 ∨ c i = -1) (hd : ∀ i, d i = 1 ∨ d i = -1)
    (hsum : Matrix.circulant a * (Matrix.circulant a).transpose
        + Matrix.circulant b * (Matrix.circulant b).transpose
        + Matrix.circulant c * (Matrix.circulant c).transpose
        + Matrix.circulant d * (Matrix.circulant d).transpose
        = (4 * m + 4 : ℤ) • (1 : Matrix (Fin m) (Fin m) ℤ) - 4 • Matrix.of (fun _ _ => (1 : ℤ)))
    (hsa : ∑ i, a i = 2) (hsb : ∑ i, b i = 0) (hsc : ∑ i, c i = 0) (hsd : ∑ i, d i = 0) :
    IsHadamardMatrix (bordered_goethals_seidel_matrix (Matrix.circulant a) (Matrix.circulant b)
      (Matrix.circulant c) (Matrix.circulant d)) := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hsa
  have : NeZero m := ⟨hm0⟩
  refine ⟨bordered_goethals_seidel_matrix_entries a b c d ha hb hc hd, ?_⟩
  rw [bordered_goethals_seidel_matrix, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  have hcard : (Fintype.card (Fin 4 ⊕ Fin 4 × Fin m) : ℤ) = 4 * m + 4 := by
    simp; ring
  rw [hcard, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero]
  have h12 := bordered_goethals_seidel_cross_block a b c d hsa hsb hsc hsd
  refine Matrix.fromBlocks_inj.mpr ⟨bordered_goethals_seidel_corner_block m, h12, ?_,
    bordered_goethals_seidel_lower_block a b c d hsum⟩
  have := congrArg Matrix.transpose h12
  rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.transpose_zero] at this
  exact this
