import AFTD.Prelude

/-!
# ose_quad_inequality

Topic: algorithms   Node: 5dbaa5f7df8f

Provenance: helper lemma. arXiv:2611.08546, Section 6.1; Boolean-cube distortion argument

For four points in a real inner-product space, the sum of squared distances along either pair of opposite diagonals is at most the sum of the four squared side lengths.
-/

private lemma ose_quad_vectors (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (x y z : H) :
    ‖x+y‖^2 + ‖y+z‖^2 ≤ ‖x‖^2 + ‖z‖^2 + ‖x+y+z‖^2 + ‖y‖^2 := by
  have hxy := norm_add_sq_real x y
  have hyz := norm_add_sq_real y z
  have hxyz := norm_add_sq_real (x+y) z
  have hxz := norm_add_sq_real x z
  simp only [inner_add_left] at hxyz
  nlinarith [sq_nonneg ‖x+z‖]

lemma ose_quad_inequality (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a b c d : H) :
    dist a d^2 + dist b c^2 ≤ dist a b^2 + dist c d^2 + dist a c^2 + dist b d^2 := by
  let x := a-b
  let y := b-d
  let z := d-c
  have h := ose_quad_vectors H x y z
  have e1 : a-d = x+y := by dsimp [x,y]; abel
  have e2 : b-c = y+z := by dsimp [y,z]; abel
  have e3 : a-c = x+y+z := by dsimp [x,y,z]; abel
  have e4 : c-d = -z := by dsimp [z]; abel
  simp only [dist_eq_norm]
  rw [e1,e2,e3,e4,norm_neg]
  exact h
