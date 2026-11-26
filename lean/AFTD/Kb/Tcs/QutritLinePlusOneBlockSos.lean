import AFTD.Prelude

/-!
# qutrit_line_plus_one_block_sos

Topic: quantum   Node: 3efcfbfd9f61

Provenance: helper lemma. OP-2299 line-plus-point symmetric-extension bound, exact experiment 41004.

A rational three-variable quadratic form appearing in the symmetric-extension line-plus-point bound is a sum of squares. Apply separately to real and imaginary parts.
-/

theorem qutrit_line_plus_one_block_sos (a b c : ℝ) :
    3*a^2 + 3*b^2 + 8*c^2 - 4*(a*b+a*c+b*c) =
      ((3*a-2*b-2*c)^2 + 5*(b-2*c)^2)/3 := by
  ring
