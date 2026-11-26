import AFTD.Prelude

/-!
# qutrit_cyclic_boundary_uniform_two_copy_sos

Topic: quantum   Node: 4fc004c58a24

Provenance: helper lemma. OP-2299; exact rational SOS decomposition, experiment 40308.

A uniform polynomial sum-of-squares identity for a rationally parameterized cyclic boundary witness family. Capital variables may be specialized to conjugates and the parameter to a real number. The SOS-to-extension dual transfer remains separate.
-/

theorem qutrit_cyclic_boundary_uniform_two_copy_sos
    (x0 x1 x2 X0 X1 X2 y0 y1 y2 Y0 Y1 Y2 t : ℂ) :
    360*(y0*Y0 + y1*Y1 + y2*Y2)*(x0*X0*((1-t)^2*(y0*Y0) + t^2*(y2*Y2) + (y1*Y1)) + x1*X1*((1-t)^2*(y2*Y2) + t^2*(y1*Y1) + (y0*Y0)) + x2*X2*((1-t)^2*(y1*Y1) + t^2*(y0*Y0) + (y2*Y2)) - (1 - t + t^2)*(X0*x1*Y0*y2 + X0*x2*Y0*y1 + X1*x0*Y2*y0 + X1*x2*Y2*y1 + X2*x0*Y1*y0 + X2*x1*Y1*y2)) =
      (90)*((2)*(x0*y0*Y0) + (-2)*(x0*y0*Y0*t) + (1)*(x0*y1*Y1) + (-1)*(x0*y2*Y2*t) + (-1)*(x1*y2*Y0) + (2)*(x1*y2*Y0*t) + (-2)*(x2*y1*Y0) + (1)*(x2*y1*Y0*t))*((2)*(X0*Y0*y0) + (-2)*(X0*Y0*y0*t) + (1)*(X0*Y1*y1) + (-1)*(X0*Y2*y2*t) + (-1)*(X1*Y2*y0) + (2)*(X1*Y2*y0*t) + (-2)*(X2*Y1*y0) + (1)*(X2*Y1*y0*t)) +
      (30)*((3)*(x0*y1*Y1) + (3)*(x0*y2*Y2*t) + (-3)*(x1*y2*Y0) + (-3)*(x2*y1*Y0*t))*((3)*(X0*Y1*y1) + (3)*(X0*Y2*y2*t) + (-3)*(X1*Y2*y0) + (-3)*(X2*Y1*y0*t)) +
      (3)*((6)*(x1*y0*Y1) + (-3)*(x1*y0*Y1*t) + (-6)*(x2*y0*Y2) + (3)*(x2*y0*Y2*t))*((6)*(X1*Y0*y1) + (-3)*(X1*Y0*y1*t) + (-6)*(X2*Y0*y2) + (3)*(X2*Y0*y2*t)) +
      (1)*((9)*(x1*y0*Y1*t) + (-9)*(x2*y0*Y2*t))*((9)*(X1*Y0*y1*t) + (-9)*(X2*Y0*y2*t)) +
      (90)*((2)*(x0*y0*Y1) + (-1)*(x0*y0*Y1*t) + (1)*(x1*y2*Y1) + (1)*(x1*y2*Y1*t) + (-1)*(x2*y0*Y0*t) + (-1)*(x2*y1*Y1) + (1)*(x2*y1*Y1*t) + (-2)*(x2*y2*Y2))*((2)*(X0*Y0*y1) + (-1)*(X0*Y0*y1*t) + (1)*(X1*Y2*y1) + (1)*(X1*Y2*y1*t) + (-1)*(X2*Y0*y0*t) + (-1)*(X2*Y1*y1) + (1)*(X2*Y1*y1*t) + (-2)*(X2*Y2*y2)) +
      (30)*((3)*(x0*y0*Y1*t) + (-3)*(x1*y2*Y1) + (3)*(x1*y2*Y1*t) + (-3)*(x2*y0*Y0*t) + (3)*(x2*y1*Y1) + (-3)*(x2*y1*Y1*t))*((3)*(X0*Y0*y1*t) + (-3)*(X1*Y2*y1) + (3)*(X1*Y2*y1*t) + (-3)*(X2*Y0*y0*t) + (3)*(X2*Y1*y1) + (-3)*(X2*Y1*y1*t)) +
      (3)*((6)*(x0*y1*Y2) + (-3)*(x0*y1*Y2*t) + (-6)*(x1*y1*Y0) + (3)*(x1*y1*Y0*t))*((6)*(X0*Y1*y2) + (-3)*(X0*Y1*y2*t) + (-6)*(X1*Y1*y0) + (3)*(X1*Y1*y0*t)) +
      (1)*((9)*(x0*y1*Y2*t) + (-9)*(x1*y1*Y0*t))*((9)*(X0*Y1*y2*t) + (-9)*(X1*Y1*y0*t)) +
      (90)*((2)*(x0*y0*Y2) + (-1)*(x0*y0*Y2*t) + (-1)*(x1*y0*Y0) + (1)*(x1*y1*Y1*t) + (-2)*(x1*y2*Y2) + (2)*(x1*y2*Y2*t) + (1)*(x2*y1*Y2) + (-2)*(x2*y1*Y2*t))*((2)*(X0*Y0*y2) + (-1)*(X0*Y0*y2*t) + (-1)*(X1*Y0*y0) + (1)*(X1*Y1*y1*t) + (-2)*(X1*Y2*y2) + (2)*(X1*Y2*y2*t) + (1)*(X2*Y1*y2) + (-2)*(X2*Y1*y2*t)) +
      (30)*((3)*(x0*y0*Y2*t) + (-3)*(x1*y0*Y0) + (-3)*(x1*y1*Y1*t) + (3)*(x2*y1*Y2))*((3)*(X0*Y0*y2*t) + (-3)*(X1*Y0*y0) + (-3)*(X1*Y1*y1*t) + (3)*(X2*Y1*y2)) +
      (3)*((6)*(x0*y2*Y1) + (-3)*(x0*y2*Y1*t) + (-6)*(x2*y2*Y0) + (3)*(x2*y2*Y0*t))*((6)*(X0*Y2*y1) + (-3)*(X0*Y2*y1*t) + (-6)*(X2*Y2*y0) + (3)*(X2*Y2*y0*t)) +
      (1)*((9)*(x0*y2*Y1*t) + (-9)*(x2*y2*Y0*t))*((9)*(X0*Y2*y1*t) + (-9)*(X2*Y2*y0*t)) +
      (9)*((4)*(x0*Y1*Y2) + (-2)*(x0*Y1*Y2*t) + (-2)*(x1*Y0*Y1) + (1)*(x1*Y0*Y1*t) + (-2)*(x2*Y0*Y2) + (1)*(x2*Y0*Y2*t))*((4)*(X0*y1*y2) + (-2)*(X0*y1*y2*t) + (-2)*(X1*y0*y1) + (1)*(X1*y0*y1*t) + (-2)*(X2*y0*y2) + (1)*(X2*y0*y2*t)) +
      (3)*((6)*(x0*Y1*Y2*t) + (-3)*(x1*Y0*Y1*t) + (-3)*(x2*Y0*Y2*t))*((6)*(X0*y1*y2*t) + (-3)*(X1*y0*y1*t) + (-3)*(X2*y0*y2*t)) +
      (3)*((6)*(x1*Y0*Y1) + (-3)*(x1*Y0*Y1*t) + (-6)*(x2*Y0*Y2) + (3)*(x2*Y0*Y2*t))*((6)*(X1*y0*y1) + (-3)*(X1*y0*y1*t) + (-6)*(X2*y0*y2) + (3)*(X2*y0*y2*t)) +
      (1)*((9)*(x1*Y0*Y1*t) + (-9)*(x2*Y0*Y2*t))*((9)*(X1*y0*y1*t) + (-9)*(X2*y0*y2*t)) := by ring
