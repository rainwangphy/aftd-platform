import AFTD.Prelude

/-!
# one_strongly_euclidean_sphere_squared_distance_identity

Topic: algorithms   Node: 0e4388a1310a

Provenance: helper lemma. OP-1304: squared-distance identity for the spherical extension.

If two vectors in a real inner-product space both have squared norm q²/4, the squared norm of x−t y equals (1−t)²q²/4+t times the squared norm of x−y.
-/

theorem one_strongly_euclidean_sphere_squared_distance_identity (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x y : H) (t q : ℝ) (hx : ‖x‖^2 = q^2/4) (hy : ‖y‖^2 = q^2/4) :
    ‖x - t • y‖^2 = (1-t)^2 * q^2/4 + t * ‖x-y‖^2 := by
  have hxy := norm_sub_sq_real x y
  have ht := norm_sub_sq_real x (t • y)
  simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at ht
  have hm := congrArg (fun z : ℝ => t*z) hxy
  nlinarith
