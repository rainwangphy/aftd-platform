import AFTD.Prelude

/-!
# qutrit_real_witness_first_multiplier_sos

Topic: quantum   Node: 9eba5c0652c7

Provenance: helper lemma. OP-2299; qutrit convolution, experiments 40125-40126 and 40163-40166.

An exact identity in the qutrit Bell-orbit and real witness reduction.
-/

theorem qutrit_real_witness_first_multiplier_sos
    (x0 x1 x2 y0 y1 y2 : ℝ) :
    let z0 := x0*y1*y2
    let z1 := x1*y2*y0
    let z2 := x2*y0*y1
    let a0 := x0*y1^2
    let a1 := x1*y2^2
    let a2 := x2*y0^2
    let b0 := x2*y0*y2
    let b1 := x0*y1*y0
    let b2 := x1*y2*y1
    let c0 := y0*(x0*y0-x1*y1)
    let c1 := y1*(x1*y1-x2*y2)
    let c2 := y2*(x2*y2-x0*y0)
    4*(y0^2+y1^2+y2^2)*
      (x0^2*y0^2+x1^2*y1^2+x2^2*y2^2 +
       2*(x0^2*y1^2+x1^2*y2^2+x2^2*y0^2) -
       2*(x0*x1*y0*y1+x1*x2*y1*y2+x0*x2*y0*y2)) =
    4*(z0^2+z1^2+z2^2) +
      2*((z0-z1)^2+(z1-z2)^2+(z2-z0)^2) +
      (4*(a0+c0)^2+(2*b0-a0)^2+3*a0^2) +
      (4*(a1+c1)^2+(2*b1-a1)^2+3*a1^2) +
      (4*(a2+c2)^2+(2*b2-a2)^2+3*a2^2) := by
  dsimp
  ring
