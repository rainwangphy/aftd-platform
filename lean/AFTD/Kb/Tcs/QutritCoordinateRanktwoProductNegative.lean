import AFTD.Prelude
import AFTD.Kb.Tcs.QutritCoordinateRanktwoProductEval

/-!
# qutrit_coordinate_ranktwo_product_negative

Topic: quantum   Node: 411931782859

Provenance: helper lemma. OP-2299 coordinate rank-two candidate refutation; experiments 41022 and 41025.

The displayed nontrivial part of the rank-two local Hessian candidate family has an explicit negative product evaluation, so this family cannot provide positive witnesses.
-/

theorem qutrit_coordinate_ranktwo_product_negative (s t : ℝ)
    (h : s^2+t^2=1) (hs : s ≠ 0) (ht : t ≠ 0) :
    (-t)^2 * (2*s^2*t*(-t) + s^2*(-t)^2 - s^2 - t^2 + 1) < 0 := by
  rw [qutrit_coordinate_ranktwo_product_eval s t h]
  have hp : 0 < s^2*t^4 := by positivity
  linarith
