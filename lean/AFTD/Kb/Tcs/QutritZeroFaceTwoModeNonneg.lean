import AFTD.Prelude
import AFTD.Kb.Tcs.QutritZeroFaceTwoModeSos

/-!
# qutrit_zero_face_two_mode_nonneg

Topic: quantum   Node: 257fe3b2fd77

Provenance: helper lemma. OP-2299 zero-Bell face rank-one witness, exact experiments 40958 and 40971.

The two-mode zero-face expression is nonnegative when both Fourier coefficients are nonnegative.
-/

theorem qutrit_zero_face_two_mode_nonneg
    (a b c d g z r : ℝ) (hr : r^2 = 3)
    (hminus : 0 ≤ g-r*z) (hplus : 0 ≤ g+r*z) :
    0 ≤ g * (3*a^2 + 3*b^2 + c^2 + d^2) / 2 + 3*z*(a*d-b*c) := by
  have h₁ : 0 ≤ (g-r*z) * ((3*a-r*d)^2+(3*b+r*c)^2) / 4 := by positivity
  have h₂ : 0 ≤ (g+r*z) * ((3*a+r*d)^2+(3*b-r*c)^2) / 4 := by positivity
  have heq := qutrit_zero_face_two_mode_sos a b c d g z r hr
  linarith
