import AFTD.Prelude

/-!
# cube_roots_of_unity_sub_sq

Topic: graphs   Node: 2be565c63eea

Provenance: helper lemma. arXiv:2610.41820 Lemma 2.4(a)

For any two distinct complex cube roots of unity x and y, (x - y)^2 = -3 * x * y.
-/

/-- The square of the difference of two distinct complex cube roots of unity equals minus three times their product. -/
theorem cube_roots_of_unity_sub_sq (x y : ℂ) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hxy : x ≠ y) :
    (x - y) ^ 2 = -3 * x * y := by
  have hfac : (x - y) * (x ^ 2 + x * y + y ^ 2) = 0 := by
    rw [show (x - y) * (x ^ 2 + x * y + y ^ 2) = x ^ 3 - y ^ 3 by ring, hx, hy, sub_self]
  have hsum : x ^ 2 + x * y + y ^ 2 = 0 := by
    exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hxy)
  rw [show (x - y) ^ 2 = (x ^ 2 + x * y + y ^ 2) - 3 * x * y by ring, hsum]
  ring
