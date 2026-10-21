import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidCommonListColorableOneOfColorableOne
import AFTD.Kb.Tcs.MatroidCommonListColorableMono
import AFTD.Kb.Tcs.MatroidCommonListColorable
import AFTD.Kb.Tcs.MatroidCommonColorable

/-!
# matroid_common_list_colorable_two_of_colorable_one

Topic: combinatorics   Node: efb34999d123

Provenance: helper lemma. step towards matroid_common_list_colorable_succ_of_common_colorable

If two matroids have a common coloring with 1 color, then they are 2-list-colorable (immediate from 1-list-colorability and monotonicity).
-/

/-- Base case k = 1 of one-step list-lifting: if two matroids on a common ground set have a common coloring with 1 color, then they are 2-list-colorable. -/
theorem matroid_common_list_colorable_two_of_colorable_one {α : Type*} (M₁ M₂ : Matroid α)
    (h : matroid_common_colorable M₁ M₂ 1) :
    matroid_common_list_colorable M₁ M₂ 2 := by
  exact matroid_common_list_colorable_mono M₁ M₂ (by norm_num)
    (matroid_common_list_colorable_one_of_colorable_one M₁ M₂ h)
