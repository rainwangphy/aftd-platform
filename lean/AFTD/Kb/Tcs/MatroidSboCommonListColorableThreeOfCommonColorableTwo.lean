import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidSboCommonListColorableTwoOfCommonColorableTwo
import AFTD.Kb.Tcs.MatroidCommonListColorableMono
import AFTD.Kb.Tcs.MatroidCommonListColorable
import AFTD.Kb.Tcs.MatroidStronglyBaseOrderable
import AFTD.Kb.Tcs.MatroidCommonColorable

/-!
# matroid_sbo_common_list_colorable_three_of_common_colorable_two

Topic: combinatorics   Node: 1b577beb8174

Provenance: helper lemma. step towards matroid_common_list_colorable_succ_of_common_colorable

If two finite strongly base-orderable matroids have a common coloring with two colors, they are 3-list-colorable (immediate from 2-list-colorability and monotonicity).
-/

/-- The k = 2 case of one-step list-lifting for strongly base-orderable matroids: if two strongly base-orderable matroids have a common 2-coloring, they are 3-list-colorable. -/
theorem matroid_sbo_common_list_colorable_three_of_common_colorable_two {α : Type*}
    (M₁ M₂ : Matroid α) [M₁.Finite] (hE : M₁.E = M₂.E)
    (h₁ : matroid_strongly_base_orderable M₁) (h₂ : matroid_strongly_base_orderable M₂)
    (h : matroid_common_colorable M₁ M₂ 2) :
    matroid_common_list_colorable M₁ M₂ 3 := by
  exact matroid_common_list_colorable_mono M₁ M₂ (by norm_num)
    (matroid_sbo_common_list_colorable_two_of_common_colorable_two M₁ M₂ hE h₁ h₂ h)
