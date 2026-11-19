import AFTD.Prelude
import AFTD.Kb.Tcs.ThreePointRatio

/-!
# three_point_ratio_ne_one

Topic: information   Node: 2ac99f6938a9

Provenance: formalization of a published result. Source: arXiv:2611.21275, Section III-A

In a field F, if a ≠ b and b ≠ c, then three_point_ratio a b c ≠ 1.
-/

/-- The three-point ratio (c - a) / (b - a) is not equal to 1 when a ≠ b and b ≠ c. -/
theorem three_point_ratio_ne_one {F : Type*} [Field F] {a b c : F} (hab : a ≠ b) (hbc : b ≠ c) : three_point_ratio a b c ≠ 1 := by
  intro h
  rw [three_point_ratio] at h
  rw [div_eq_one_iff_eq (sub_ne_zero.mpr (Ne.symm hab))] at h
  exact hbc (sub_left_injective h).symm
