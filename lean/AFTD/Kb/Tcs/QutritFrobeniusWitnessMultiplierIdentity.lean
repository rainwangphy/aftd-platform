import AFTD.Prelude

/-!
# qutrit_frobenius_witness_multiplier_identity

Topic: quantum   Node: 5c84b989aaa2

Provenance: helper lemma. OP-2299; Frobenius-contraction witness SOS route, experiment 40249.

An exact algebraic identity behind a two-copy sum-of-squares certificate for Frobenius-contraction witnesses. Uppercase variables may later be specialized to complex conjugates; the identity itself is formal polynomial algebra.
-/

theorem qutrit_frobenius_witness_multiplier_identity
    (x0 x1 x2 X0 X1 X2 a b c u U v V w W t : ℂ) :
    2*t*(t*(x0*X0 + x1*X1 + x2*X2)-(X0*(a*x0 + u*x1 + v*x2) + X1*(U*x0 + b*x1 + w*x2) + X2*(V*x0 + W*x1 + c*x2))) =
      (t*x0-(a*x0 + u*x1 + v*x2))*(t*X0-(a*X0 + U*X1 + V*X2)) +
      (t*x1-(U*x0 + b*x1 + w*x2))*(t*X1-(u*X0 + b*X1 + W*X2)) +
      (t*x2-(V*x0 + W*x1 + c*x2))*(t*X2-(v*X0 + w*X1 + c*X2)) +
      (t^2-(a^2 + b^2 + c^2 + 2*(u*U+v*V+w*W)))*(x0*X0 + x1*X1 + x2*X2) +
      (a*x1-U*x0)*(a*X1-u*X0) +
      (a*x2-V*x0)*(a*X2-v*X0) +
      (U*x2-V*x1)*(u*X2-v*X1) +
      (u*x1-b*x0)*(U*X1-b*X0) +
      (u*x2-W*x0)*(U*X2-w*X0) +
      (b*x2-W*x1)*(b*X2-w*X1) +
      (v*x1-w*x0)*(V*X1-W*X0) +
      (v*x2-c*x0)*(V*X2-c*X0) +
      (w*x2-c*x1)*(W*X2-c*X1) := by ring
