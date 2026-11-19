import AFTD.Prelude
import AFTD.Kb.Tcs.ThreePointRatio

/-!
# three_point_ratio_ne_zero

Topic: information   Node: 675431fe72f6

Provenance: formalization of a published result. Source: arXiv:2611.21275, Section III-A

In a field F, if a ≠ b and a ≠ c, then three_point_ratio a b c ≠ 0.
-/

/-- The three-point ratio (c - a) / (b - a) is nonzero when a ≠ b and a ≠ c. -/
theorem three_point_ratio_ne_zero {F : Type*} [Field F] {a b c : F} (hab : a ≠ b) (hac : a ≠ c) : three_point_ratio a b c ≠ 0 := by
  dsimp [three_point_ratio]
  exact div_ne_zero (sub_ne_zero.mpr hac.symm) (sub_ne_zero.mpr hab.symm)
