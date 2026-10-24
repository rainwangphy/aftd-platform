import AFTD.Prelude
import AFTD.Kb.Optimization.MatrixHasPsdFactorization

/-!
# matrix_has_psd_factorization_submatrix

Topic: integer_programming   Node: 81ec84dbe052

Provenance: helper lemma. Helper for permutahedron_five_xc_psd_ge_six (arXiv:2610.04498 Sec. 4.2).

If a real matrix M has a positive semidefinite factorization of size r, then so does every submatrix M.submatrix f g (rows reindexed by f, columns by g): keep the factors of the chosen rows and columns.
-/

theorem matrix_has_psd_factorization_submatrix {m n m' n' : Type*} (M : Matrix m n ℝ) (r : ℕ)
    (f : m' → m) (g : n' → n) (h : matrix_has_psd_factorization M r) :
    matrix_has_psd_factorization (M.submatrix f g) r := by
  obtain ⟨A, B, hA, hB, hM⟩ := h
  exact ⟨fun i => A (f i), fun j => B (g j), fun i => hA _, fun j => hB _, fun i j => hM _ _⟩
