import AFTD.Prelude

/-!
# ghz_sign_symmetry_nonzero

Topic: quantum   Node: 75faa2654375

Provenance: helper lemma.

For unit real vectors x,y,z the six displayed components cannot all vanish; consequently this polynomial map has the seven prescribed independent sign symmetries and never vanishes.
-/

theorem ghz_sign_symmetry_nonzero
    (x1 x2 x3 y1 y2 y3 z1 z2 z3 : ℝ)
    (hx : x1^2 + x2^2 + x3^2 = 1)
    (hy : y1^2 + y2^2 + y3^2 = 1)
    (hz : z1^2 + z2^2 + z3^2 = 1) :
    ¬ (x1 = 0 ∧ y1 = 0 ∧ z1 = 0 ∧
      x2*y3 - x3*y2 = 0 ∧ x2*z3 - x3*z2 = 0 ∧
      y2*z2 + y3*z3 = 0) := by
  rintro ⟨hx1, hy1, hz1, hxy, hxz, hyz⟩
  have hx' : x2^2 + x3^2 = 1 := by nlinarith only [hx, hx1]
  have hy' : y2^2 + y3^2 = 1 := by nlinarith only [hy, hy1]
  have hz' : z2^2 + z3^2 = 1 := by nlinarith only [hz, hz1]
  have h2 : x2 * (y2*z3 - y3*z2) = 0 := by
    linear_combination y2 * hxz - z2 * hxy
  have h3 : x3 * (y2*z3 - y3*z2) = 0 := by
    linear_combination y3 * hxz - z3 * hxy
  have hd : y2*z3 - y3*z2 = 0 := by
    by_cases h : x2 = 0
    · have h' : x3 ≠ 0 := by
        intro q
        nlinarith only [hx', h, q]
      exact (mul_eq_zero.mp h3).resolve_left h'
    · exact (mul_eq_zero.mp h2).resolve_left h
  have hid : (y2*z2 + y3*z3)^2 + (y2*z3 - y3*z2)^2 =
      (y2^2 + y3^2) * (z2^2 + z3^2) := by ring
  rw [hyz, hd, hy', hz'] at hid
  norm_num at hid
