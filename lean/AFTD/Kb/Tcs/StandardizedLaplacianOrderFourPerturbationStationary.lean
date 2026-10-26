import AFTD.Prelude
import AFTD.Kb.Tcs.PositiveMatrixOrderFourLeftStationary
import AFTD.Kb.Tcs.StandardizedLaplacianOrderFourDiagonalLtOne
import AFTD.Kb.Tcs.MatrixOrderFourCenteredShift
import AFTD.Kb.Tcs.IsStandardizedLaplacian

/-!
# standardized_laplacian_order_four_perturbation_stationary

Topic: graphs   Node: a0dc0e9eb7ad

Provenance: helper lemma. Sector-bound formalization for IN-166; arXiv:math/0508176, Theorem 5.

Every positive centered scalar shift of an order-four standardized Laplacian has a strictly positive left null vector.
-/

theorem standardized_laplacian_order_four_perturbation_stationary
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : is_standardized_laplacian 4 L)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ π : Fin 4 → ℝ, (∀ i, 0 < π i) ∧
      ∀ j, ∑ i, π i * matrix_order_four_centered_shift L δ i j = 0 := by
  let M : Matrix (Fin 4) (Fin 4) ℝ :=
    fun i j => (if i = j then 1 else 0) - L i j + δ / 4
  have hM : ∀ i j, 0 < M i j := by
    intro i j
    by_cases hij : i = j
    · subst j
      dsimp only [M]
      rw [if_pos rfl]
      linarith [standardized_laplacian_order_four_diagonal_lt_one L hL i]
    · dsimp only [M]
      rw [if_neg hij]
      linarith [(hL.2 i j hij).2]
  have hrow : ∀ i, ∑ j, M i j = 1 + δ := by
    intro i
    simp [M, Finset.sum_add_distrib, Finset.sum_sub_distrib, hL.1]
    <;> ring
  obtain ⟨π, hπ, hsum, hstat⟩ := positive_matrix_order_four_left_stationary M hM (1 + δ) hrow
  refine ⟨π, hπ, ?_⟩
  intro j
  have hsj := hstat j
  simp [M, mul_add, mul_sub, mul_ite, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.sum_mul, hsum] at hsj
  simp [matrix_order_four_centered_shift, mul_add, mul_sub, mul_ite, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.sum_mul, hsum]
  linarith
