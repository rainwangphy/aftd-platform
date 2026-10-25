import AFTD.Prelude
import AFTD.Kb.Tcs.IsStandardizedLaplacianTwoFractional
import AFTD.Kb.Tcs.IsStandardizedLaplacian

/-!
# exists_nonzero_two_fractional_standardized_laplacian_four

Topic: graphs   Node: 80a7f2c1d81f

Provenance: helper lemma. step towards op_465_standardized_laplacian_order_four_polygon_conjecture

There exists a nonzero 4 × 4 real matrix that is a standardized Laplacian with at most two fractional off-diagonal entries per row (e.g. the standardized Laplacian of a directed 4-cycle, whose off-diagonal entries are all 0 or -1/4).
-/

/-- A concrete nonzero 4x4 matrix with row sums 0 and off-diagonal entries in [-1/4, 0]. -/
noncomputable def exists_nonzero_two_fractional_standardized_laplacian_four_matrix :
    Matrix (Fin 4) (Fin 4) ℝ :=
  !![ 1/4, -1/4,  0,    0;
     -1/4,  1/4,  0,    0;
        0,    0,  0,    0;
        0,    0,  0,    0]

/-- The off-diagonal entries of the concrete matrix are never strictly between -1/4 and 0. -/
lemma exists_nonzero_two_fractional_standardized_laplacian_four_matrix_no_frac
    (i j : Fin 4) (hij : j ≠ i) :
    ¬ (-1 / ↑(4 : ℕ) < exists_nonzero_two_fractional_standardized_laplacian_four_matrix i j ∧
       exists_nonzero_two_fractional_standardized_laplacian_four_matrix i j < 0) := by
  dsimp [exists_nonzero_two_fractional_standardized_laplacian_four_matrix]
  fin_cases i <;> fin_cases j
  all_goals
    first
    | exact (hij rfl).elim
    | intro h
      rcases h with ⟨h1, h2⟩
      revert h1 h2
      norm_num

/-- Sanity witness: the two-fractional standardized Laplacians of order 4 are a nonempty class containing a nonzero matrix. -/
theorem exists_nonzero_two_fractional_standardized_laplacian_four :
    ∃ L : Matrix (Fin 4) (Fin 4) ℝ, is_standardized_laplacian_two_fractional 4 L ∧ L ≠ 0 := by
  use exists_nonzero_two_fractional_standardized_laplacian_four_matrix
  constructor
  · constructor
    · constructor
      · intro i
        fin_cases i <;> { simp [Fin.sum_univ_four, exists_nonzero_two_fractional_standardized_laplacian_four_matrix]; try norm_num }
      · intro i j hij
        fin_cases i <;> fin_cases j <;> first | contradiction | norm_num [exists_nonzero_two_fractional_standardized_laplacian_four_matrix]
    · intro i
      have h_empty : (Finset.filter (fun j => j ≠ i ∧ -1 / ↑(4 : ℕ) < exists_nonzero_two_fractional_standardized_laplacian_four_matrix i j ∧
          exists_nonzero_two_fractional_standardized_laplacian_four_matrix i j < 0) Finset.univ) = ∅ := by
        apply Finset.filter_false_of_mem
        intro j _ hj
        exact exists_nonzero_two_fractional_standardized_laplacian_four_matrix_no_frac i j hj.1 hj.2
      rw [Finset.card_eq_zero.mpr h_empty]
      norm_num
  · intro h
    have h0 : exists_nonzero_two_fractional_standardized_laplacian_four_matrix 0 0 = 0 := by
      rw [h]
      rfl
    revert h0
    dsimp [exists_nonzero_two_fractional_standardized_laplacian_four_matrix]
    norm_num
