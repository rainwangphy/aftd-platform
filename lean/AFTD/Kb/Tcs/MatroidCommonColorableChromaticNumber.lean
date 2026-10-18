import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidCommonListColorableOfNcardLe
import AFTD.Kb.Tcs.MatroidCommonColorableOfListColorable
import AFTD.Kb.Tcs.MatroidCommonColorable
import AFTD.Kb.Tcs.MatroidCommonChromaticNumber

/-!
# matroid_common_colorable_chromatic_number

Topic: combinatorics   Node: 1ae89edecf55

Provenance: helper lemma. step towards matroid_common_list_chromatic_le_add_const

The common chromatic number is attained: for two loopless matroids on a common finite ground set, the pair has a common coloring with exactly χ(M₁, M₂) colors; i.e. χ(M₁, M₂) is the least element of {k | matroid_common_colorable M₁ M₂ k}.
-/

/-- The common chromatic number χ(M₁,M₂) is realized by an actual common coloring. -/
theorem matroid_common_colorable_chromatic_number {α : Type*} (M₁ M₂ : Matroid α) [Finite α] (h₁ : M₁.Loopless) (h₂ : M₂.Loopless) (hE : M₁.E = M₂.E) :
    matroid_common_colorable M₁ M₂ (matroid_common_chromatic_number M₁ M₂) := by
  unfold matroid_common_chromatic_number
  have hne : ({k | matroid_common_colorable M₁ M₂ k}).Nonempty :=
    ⟨M₁.E.ncard, matroid_common_colorable_of_list_colorable M₁ M₂ _
      (matroid_common_list_colorable_of_ncard_le M₁ M₂ h₁ h₂ hE _ (le_refl _))⟩
  exact Nat.sInf_mem hne
