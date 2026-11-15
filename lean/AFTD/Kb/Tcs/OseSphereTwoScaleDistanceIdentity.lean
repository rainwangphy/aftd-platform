import AFTD.Prelude

/-!
# ose_sphere_two_scale_distance_identity

Topic: algorithms   Node: 9fbb05f50599

Provenance: helper lemma. arXiv:2611.08546, Section 6.1; spherical two-layer construction

For two vectors on the same sphere of squared radius q²/4, the squared distance after independent radial scalings beta and alpha equals (beta-alpha)²q²/4 plus alpha*beta times their original squared distance.
-/

theorem ose_sphere_two_scale_distance_identity (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (x y : H) (α β q : ℝ) (hx : ‖x‖ ^ 2 = q ^ 2 / 4) (hy : ‖y‖ ^ 2 = q ^ 2 / 4) : ‖β • x - α • y‖ ^ 2 = (β - α) ^ 2 * q ^ 2 / 4 + α * β * ‖x - y‖ ^ 2 := by
  have hxy := norm_sub_sq_real x y
  have hscaled := norm_sub_sq_real (β • x) (α • y)
  simp only [real_inner_smul_left, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hscaled
  have hm := congrArg (fun z : ℝ => (α*β)*z) hxy
  nlinarith [hm]
