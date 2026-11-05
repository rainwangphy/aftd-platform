import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopes

/-!
# good_slopes_refl_three

Topic: elementary_number_theory   Node: 4c244c89e996

Provenance: helper lemma. arXiv:2611.04551 Section 2

The identity permutation of ℤ/3ℤ has exactly 2 good slopes: (good_slopes 3 (Equiv.refl (ZMod 3))).card = 2.
-/

/-- The identity permutation on ZMod 3 has exactly 2 good slopes. -/
theorem good_slopes_refl_three : (good_slopes 3 (Equiv.refl (ZMod 3))).card = 2 := by decide
