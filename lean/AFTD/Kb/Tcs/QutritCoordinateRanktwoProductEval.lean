import AFTD.Prelude

/-!
# qutrit_coordinate_ranktwo_product_eval

Topic: quantum   Node: 6627a5678f83

Provenance: helper lemma. OP-2299 coordinate rank-two candidate refutation; experiments 41022 and 41025.

The exact real-product restriction of a candidate rank-two coordinate Hessian witness evaluates to a negative square product.
-/

theorem qutrit_coordinate_ranktwo_product_eval (s t : ℝ) (h : s^2+t^2=1) :
    (-t)^2 * (2*s^2*t*(-t) + s^2*(-t)^2 - s^2 - t^2 + 1) = -s^2*t^4 := by
  linear_combination -t^2*h
