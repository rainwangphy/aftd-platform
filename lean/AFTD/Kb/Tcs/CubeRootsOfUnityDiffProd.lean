import AFTD.Prelude

/-!
# cube_roots_of_unity_diff_prod

Topic: graphs   Node: 33a018b77e60

Provenance: helper lemma. arXiv:2610.41820 Eq (17)

For any pairwise distinct complex cube roots of unity z, x, y, (z - x) * (z - y) = 3 * z^2.
-/

/-- Product of differences of a cube root of unity with the other two distinct cube roots equals three times its square. -/
theorem cube_roots_of_unity_diff_prod (z x y : ℂ)
    (hz : z ^ 3 = 1) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hzx : z ≠ x) (hzy : z ≠ y) (hxy : x ≠ y) :
    (z - x) * (z - y) = 3 * z ^ 2 := by
  have hx2 : x ^ 2 + x * z + z ^ 2 = 0 := by
    have h : (x - z) * (x ^ 2 + x * z + z ^ 2) = 0 := by
      calc (x - z) * (x ^ 2 + x * z + z ^ 2) = x ^ 3 - z ^ 3 := by ring
      _ = 1 - 1 := by rw [hx, hz]
      _ = 0 := by ring
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (Ne.symm hzx))
  have hy2 : y ^ 2 + y * z + z ^ 2 = 0 := by
    have h : (y - z) * (y ^ 2 + y * z + z ^ 2) = 0 := by
      calc (y - z) * (y ^ 2 + y * z + z ^ 2) = y ^ 3 - z ^ 3 := by ring
      _ = 1 - 1 := by rw [hy, hz]
      _ = 0 := by ring
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (Ne.symm hzy))
  have hxyz : x + y + z = 0 := by
    have h : (x - y) * (x + y + z) = 0 := by
      calc (x - y) * (x + y + z) = (x ^ 2 + x * z + z ^ 2) - (y ^ 2 + y * z + z ^ 2) := by ring
      _ = 0 - 0 := by rw [hx2, hy2]
      _ = 0 := by ring
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hxy)
  linear_combination (x - z) * hxyz - hx2
