import AFTD.Prelude

/-!
# three_qubit_exchange_witness_positive_form

Topic: quantum   Node: 250d7ba4813e

Provenance: helper lemma.

The displayed quadratic form is strictly positive on every real unit vector.
-/

theorem three_qubit_exchange_witness_positive_form (x y z : ℝ)
    (hn : x^2 + y^2 + z^2 = 1) :
    0 < 10*x^2 + 2*y^2 + 8*z^2 - 8*x*y - 4*x*z + 4*y*z := by
  have hid : 10*x^2 + 2*y^2 + 8*z^2 - 8*x*y - 4*x*z + 4*y*z =
      10*(x-(2/5)*y-(1/5)*z)^2 + (2/5)*(y+3*z)^2 + 4*z^2 := by ring
  rw [hid]
  by_contra h
  have hz : z = 0 := by
    nlinarith [sq_nonneg (x-(2/5)*y-(1/5)*z), sq_nonneg (y+3*z), sq_nonneg z]
  have hy : y = 0 := by
    nlinarith [sq_nonneg (x-(2/5)*y-(1/5)*z), sq_nonneg (y+3*z)]
  have hx : x = 0 := by nlinarith [sq_nonneg (x-(2/5)*y-(1/5)*z)]
  rw [hx, hy, hz] at hn
  norm_num at hn
