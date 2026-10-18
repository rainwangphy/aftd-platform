import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidCommonListColorableOfNcardLe
import AFTD.Kb.Tcs.MatroidCommonListChromaticNumber
import AFTD.Kb.Tcs.MatroidCommonListColorable

/-!
# matroid_common_list_colorable_list_chromatic_number

Topic: combinatorics   Node: 977f77f9a079

Provenance: helper lemma. step towards matroid_common_list_chromatic_le_add_const

The common list chromatic number is attained: for two loopless matroids on a common finite ground set, the pair is k-list-colorable at k = χ_ℓ(M₁, M₂).
-/

/-- The common list chromatic number χ_ℓ(M₁,M₂) is realized by an actual list coloring. -/
theorem matroid_common_list_colorable_list_chromatic_number {α : Type*} (M₁ M₂ : Matroid α) [Finite α] (h₁ : M₁.Loopless) (h₂ : M₂.Loopless) (hE : M₁.E = M₂.E) :
    matroid_common_list_colorable M₁ M₂ (matroid_common_list_chromatic_number M₁ M₂) := by
  have := Matroid.finite_of_finite (M := M₁)
  have hne : {k | matroid_common_list_colorable M₁ M₂ k}.Nonempty :=
    ⟨_, matroid_common_list_colorable_of_ncard_le M₁ M₂ h₁ h₂ hE _ (Nat.le_refl _)⟩
  exact Nat.sInf_mem hne
