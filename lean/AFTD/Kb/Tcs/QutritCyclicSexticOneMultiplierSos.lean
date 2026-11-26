import AFTD.Prelude

/-!
# qutrit_cyclic_sextic_one_multiplier_sos

Topic: quantum   Node: 2abcc7799f3d

Provenance: helper lemma. OP-2299 zero-Bell witness analysis, exact Gram computation 41071. Classical sextic; no novelty claimed.

One squared-norm multiplier makes the cyclic nonnegative sextic from the zero-face witness determinant an explicit sum of five squares.
-/

theorem qutrit_cyclic_sextic_one_multiplier_sos (x y z : ℝ) :
    (x^2+y^2+z^2) * (x^4*y^2+y^4*z^2+z^4*x^2-3*x^2*y^2*z^2) =
      (y*z*(x^2-y^2))^2 + (x*z*(y^2-z^2))^2 +
      (x^2*y^2-2*x^2*z^2+y^2*z^2)^2/4 +
      3*(y^2*(x^2-z^2))^2/4 + (x*y*(x^2-z^2))^2 := by
  ring
