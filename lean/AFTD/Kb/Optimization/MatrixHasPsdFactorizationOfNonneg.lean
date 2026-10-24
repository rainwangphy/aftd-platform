import AFTD.Prelude
import AFTD.Kb.Optimization.MatrixHasPsdFactorization

/-!
# matrix_has_psd_factorization_of_nonneg

Topic: integer_programming   Node: ec807fdb4584

Provenance: helper lemma. Helper for permutahedron_five_xc_psd_ge_six (arXiv:2610.04498 Sec. 4.2): it makes the set in the PSD-rank infimum nonempty.

Every entrywise nonnegative real matrix with finitely many rows m has a positive semidefinite factorization of size |m|: diagonal factors, A_i the i-th diagonal unit and B_j the diagonal matrix of column j.
-/

theorem matrix_has_psd_factorization_of_nonneg {m n : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m n ℝ) (h : ∀ i j, 0 ≤ M i j) :
    matrix_has_psd_factorization M (Fintype.card m) := by
  classical
  let e := Fintype.equivFin m
  refine ⟨fun i => Matrix.diagonal (fun k => if k = e i then 1 else 0),
    fun j => Matrix.diagonal (fun k => M (e.symm k) j), ?_, ?_, ?_⟩
  · intro i
    exact Matrix.PosSemidef.diagonal (fun k => by split_ifs <;> norm_num)
  · intro j
    exact Matrix.PosSemidef.diagonal (fun k => h _ _)
  · intro i j
    rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    simp
