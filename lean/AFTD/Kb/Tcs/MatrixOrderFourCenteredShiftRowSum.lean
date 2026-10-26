import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixOrderFourCenteredShift

/-!
# matrix_order_four_centered_shift_row_sum

Topic: graphs   Node: e0bf87fa930f

Provenance: helper lemma. Sector-bound formalization for IN-166; arXiv:math/0508176, Theorem 5.

A centered scalar shift preserves zero row sums.
-/

theorem matrix_order_four_centered_shift_row_sum (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hr : ∀ i, ∑ j, L i j = 0) (b : ℝ) :
    ∀ i, ∑ j, matrix_order_four_centered_shift L b i j = 0 := by
  intro i
  simp [matrix_order_four_centered_shift, Finset.sum_add_distrib, Finset.sum_sub_distrib, hr]
  <;> ring
