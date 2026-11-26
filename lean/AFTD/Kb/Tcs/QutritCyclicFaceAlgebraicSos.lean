import AFTD.Prelude

/-!
# qutrit_cyclic_face_algebraic_sos

Topic: quantum   Node: 7f8eaea8e27c

Provenance: helper lemma. OP-2299 exact Q(ω) dual and ideal quotient computations 41079, 41083 and 41085.

The algebraic four-square identity underlying the cyclic zero-Bell PPT two-copy certificate, with conjugate variables represented independently and the two face equations and cube-root equation assumed.
-/

theorem qutrit_cyclic_face_algebraic_sos (w x0 x1 x2 X0 X1 X2 y0 y1 y2 Y0 Y1 Y2 : ℂ)
    (hw : w^2+w+1=0)
    (hg : w^2*x2*y0 + w*x1*y2 + x0*y1 = 0)
    (hgc : X0*Y1 + X1*Y2*w^2 + X2*Y0*w = 0) :
    9 * ((Y0*y0 + Y1*y1 + Y2*y2) * ((X0*Y1*w^2*x1*y2 + X0*Y1*w*x2*y0 - X0*Y1*x1*y2 - X0*Y1*x2*y0 + 3*X0*Y2*x0*y2 + 3*X1*Y0*x1*y0 + X1*Y2*w^3*x1*y2 + X1*Y2*w^2*x2*y0 + X1*Y2*w*x0*y1 - X1*Y2*x0*y1 - X1*Y2*x1*y2 - X1*Y2*x2*y0 + X2*Y0*w^4*x1*y2 + X2*Y0*w^3*x2*y0 + X2*Y0*w^2*x0*y1 - X2*Y0*x0*y1 - X2*Y0*x1*y2 - X2*Y0*x2*y0 + 3*X2*Y1*x2*y1)/3) - (X0*y0*y2 + X1*w*y0*y1 + X2*w^2*y1*y2)*(-Y0*Y1*w*x1 - Y0*Y1*x1 + Y0*Y2*x0 + Y1*Y2*w^2*x2 + 2*Y1*Y2*w*x2 + Y1*Y2*x2) - ((Y0*w^2*x0*y1 + Y0*w*x2*y0 - 2*Y0*x1*y2 + 3*Y1*x2*y1)/3)*((X0*Y1*w^2*y0 + 2*X0*Y1*w*y0 + X0*Y1*y0 - 2*X1*Y2*y0 - X2*Y0*w*y0 - X2*Y0*y0 + 3*X2*Y1*y1)/3) - ((Y1*w^2*x1*y2 + Y1*w*x0*y1 - 2*Y1*x2*y0 + 3*Y2*x0*y2)/3)*((-X0*Y1*w*y1 - X0*Y1*y1 + 3*X0*Y2*y2 + X1*Y2*w^2*y1 + 2*X1*Y2*w*y1 + X1*Y2*y1 - 2*X2*Y0*y1)/3) - (-(-3*Y0*x1*y0 - Y2*w^2*x2*y0 - Y2*w*x1*y2 + 2*Y2*x0*y1)/3)*((-2*X0*Y1*y2 + 3*X1*Y0*y0 - X1*Y2*w*y2 - X1*Y2*y2 + X2*Y0*w^2*y2 + 2*X2*Y0*w*y2 + X2*Y0*y2)/3)) = 0 := by
  linear_combination (-X0*Y0*Y1*y0 - X0*Y1^2*y1 + 8*X0*Y1*Y2*y2 - 8*X1*Y0*Y2*w*y0 + X1*Y0*Y2*y0 + 4*X1*Y1*Y2*w*y1 - 2*X1*Y1*Y2*y1 - 2*X1*Y2^2*w*y2 - 5*X1*Y2^2*y2 - 4*X2*Y0^2*w*y0 - 6*X2*Y0^2*y0 + 2*X2*Y0*Y1*w*y1 - 3*X2*Y0*Y1*y1 + 8*X2*Y0*Y2*w*y2 + 9*X2*Y0*Y2*y2)*hg + (3*(3*Y0*w*x1*y0*y2 + Y0*w*x2*y0^2 + 3*Y0*x1*y0*y2 - Y0*x2*y0^2 - Y1*w*x1*y1*y2 - Y1*w*x2*y0*y1 - 2*Y1*x1*y1*y2 - 2*Y1*x2*y0*y1 - 2*Y2*w*x1*y2^2 - Y2*x1*y2^2 + 3*Y2*x2*y0*y2))*hgc + (-X0*Y0*Y1*w^2*x0*y0*y1 - X0*Y0*Y1*w*x0*y0*y1 - X0*Y0*Y1*w*x2*y0^2 + X0*Y0*Y1*x0*y0*y1 + 5*X0*Y0*Y1*x1*y0*y2 + X0*Y1^2*w*x1*y1*y2 + X0*Y1^2*x0*y1^2 + 3*X0*Y1^2*x1*y1*y2 - 2*X0*Y1^2*x2*y0*y1 - 15*X0*Y1*Y2*x2*y0*y2 + 9*X1*Y0*Y1*x1*y0*y1 - 6*X1*Y0*Y2*w*x1*y0*y2 + 5*X1*Y0*Y2*w*x2*y0^2 + 2*X1*Y0*Y2*x0*y0*y1 + 5*X1*Y0*Y2*x1*y0*y2 - 3*X1*Y0*Y2*x2*y0^2 - X1*Y1*Y2*w^2*x1*y1*y2 - X1*Y1*Y2*w*x0*y1^2 + 5*X1*Y1*Y2*w*x1*y1*y2 - 10*X1*Y1*Y2*w*x2*y0*y1 - X1*Y1*Y2*x0*y1^2 - 3*X1*Y1*Y2*x1*y1*y2 + 5*X1*Y1*Y2*x2*y0*y1 + 9*X1*Y2^2*w*x1*y2^2 + 3*X1*Y2^2*w*x2*y0*y2 - 3*X1*Y2^2*x0*y1*y2 - 3*X1*Y2^2*x1*y2^2 - 3*X1*Y2^2*x2*y0*y2 + 3*X2*Y0^2*w^2*x1*y0*y2 + X2*Y0^2*w*x0*y0*y1 - 3*X2*Y0^2*w*x1*y0*y2 + 7*X2*Y0^2*w*x2*y0^2 + 3*X2*Y0^2*x0*y0*y1 - 8*X2*Y0^2*x1*y0*y2 - 3*X2*Y0^2*x2*y0^2 + 3*X2*Y0*Y1*w^2*x1*y1*y2 + 6*X2*Y0*Y1*w*x1*y1*y2 + X2*Y0*Y1*w*x2*y0*y1 + 3*X2*Y0*Y1*x1*y1*y2 + 5*X2*Y0*Y1*x2*y0*y1 + 3*X2*Y0*Y2*w^2*x1*y2^2 - X2*Y0*Y2*w^2*x2*y0*y2 - 4*X2*Y0*Y2*w*x1*y2^2 - 6*X2*Y0*Y2*w*x2*y0*y2 - 4*X2*Y0*Y2*x0*y1*y2 - 3*X2*Y0*Y2*x1*y2^2 - 3*X2*Y0*Y2*x2*y0*y2 - 9*X2*Y1*Y2*w^2*x2*y1*y2 - 9*X2*Y1*Y2*w*x2*y1*y2 + 9*X2*Y1*Y2*x2*y1*y2)*hw
