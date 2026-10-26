import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixOrderFourCenteredShift

/-!
# matrix_order_four_centered_shift_mulVec

Topic: graphs   Node: ab6d5c04d095

Provenance: helper lemma. Sector-bound formalization for IN-166; arXiv:math/0508176, Theorem 5.

The action of a centered scalar shift on a complex vector is its original image plus the scalar multiple of the vector minus its average.
-/

theorem matrix_order_four_centered_shift_mulVec (L : Matrix (Fin 4) (Fin 4) ℝ)
    (b : ℝ) (v : Fin 4 → ℂ) :
    ((matrix_order_four_centered_shift L b).map (algebraMap ℝ ℂ)).mulVec v =
      fun i => (L.map (algebraMap ℝ ℂ)).mulVec v i + (b : ℂ) * v i -
        (b : ℂ) / 4 * ∑ j, v j := by
  ext i
  have hcast (j : Fin 4) : ((if i = j then b else 0 : ℝ) : ℂ) =
      if i = j then (b : ℂ) else 0 := by
    by_cases hij : i = j <;> simp [hij]
  simp [matrix_order_four_centered_shift, Matrix.mulVec, dotProduct, hcast, add_mul, sub_mul, ite_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
