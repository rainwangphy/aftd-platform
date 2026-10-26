import AFTD.Prelude

/-!
# matrix_order_four_row_sum_zero_mulVec_const

Topic: graphs   Node: fbfb497437e9

Provenance: helper lemma. Sector-bound formalization for IN-166; arXiv:math/0508176, Theorem 5.

A real order-four matrix with zero row sums annihilates every complex constant vector.
-/

theorem matrix_order_four_row_sum_zero_mulVec_const (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hr : ∀ i, ∑ j, L i j = 0) (k : ℂ) :
    (L.map (algebraMap ℝ ℂ)).mulVec (fun _ => k) = 0 := by
  ext i
  change (∑ j, (algebraMap ℝ ℂ) (L i j) * k) = 0
  rw [← Finset.sum_mul, ← map_sum, hr i, map_zero, zero_mul]
