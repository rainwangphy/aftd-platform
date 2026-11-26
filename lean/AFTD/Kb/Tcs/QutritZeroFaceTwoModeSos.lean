import AFTD.Prelude

/-!
# qutrit_zero_face_two_mode_sos

Topic: quantum   Node: c637aff27cfb

Provenance: helper lemma. OP-2299 zero-Bell face rank-one witness, exact experiments 40958 and 40971.

A real polynomial identity decomposes the two-mode zero-face expression into two weighted sums of squares.
-/

theorem qutrit_zero_face_two_mode_sos
    (a b c d g z r : ℝ) (hr : r^2 = 3) :
    3 * (g * (3*a^2 + 3*b^2 + c^2 + d^2) / 2 + 3*z*(a*d-b*c)) =
      (g-r*z) * ((3*a-r*d)^2+(3*b+r*c)^2) / 4 +
      (g+r*z) * ((3*a+r*d)^2+(3*b-r*c)^2) / 4 := by
  linear_combination (-(6*a*d*z-6*b*c*z+c^2*g+d^2*g)/2) * hr
