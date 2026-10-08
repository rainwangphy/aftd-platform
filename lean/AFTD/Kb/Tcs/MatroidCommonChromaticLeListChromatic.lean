import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidCommonListColorableOfNcardLe
import AFTD.Kb.Tcs.MatroidCommonColorableOfListColorable
import AFTD.Kb.Tcs.MatroidCommonChromaticNumber
import AFTD.Kb.Tcs.MatroidCommonListChromaticNumber
import AFTD.Kb.Tcs.MatroidCommonListColorable

/-!
# matroid_common_chromatic_le_list_chromatic

Topic: combinatorics   Node: aaebe1399417

Provenance: helper lemma. Helper for arXiv:2610.07318, Question 3.2 (the inequality χ ≤ χ_ℓ that the paper uses implicitly). Proof: χ_ℓ is attained (the set is nonempty by matroid_common_list_colorable_of_ncard_le, Nat.sInf_mem), list-colorability with constant lists gives a coloring (matroid_common_colorable_of_list_colorable), then Nat.sInf_le.

For two loopless matroids on a common finite ground set, the common chromatic number is at most the common list chromatic number: χ(M₁, M₂) ≤ χ_ℓ(M₁, M₂). Hence the equality χ_ℓ = χ asked for strongly base-orderable pairs is equivalent to χ_ℓ ≤ χ.
-/

theorem matroid_common_chromatic_le_list_chromatic {α : Type*} (M₁ M₂ : Matroid α)
    [M₁.Finite] (h₁ : M₁.Loopless) (h₂ : M₂.Loopless) (hE : M₁.E = M₂.E) :
    matroid_common_chromatic_number M₁ M₂ ≤ matroid_common_list_chromatic_number M₁ M₂ := by
  have hne : {k | matroid_common_list_colorable M₁ M₂ k}.Nonempty :=
    ⟨_, matroid_common_list_colorable_of_ncard_le M₁ M₂ h₁ h₂ hE _ le_rfl⟩
  exact Nat.sInf_le (matroid_common_colorable_of_list_colorable M₁ M₂ _ (Nat.sInf_mem hne))
