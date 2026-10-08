import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidSboCommonListColorableTwoOfCommonColorableTwo
import AFTD.Kb.Tcs.MatroidCommonChromaticLeListChromatic
import AFTD.Kb.Tcs.MatroidCommonListColorableOfNcardLe
import AFTD.Kb.Tcs.MatroidCommonColorableOfListColorable
import AFTD.Kb.Tcs.MatroidCommonListColorableOneOfColorableOne
import AFTD.Kb.Tcs.MatroidCommonChromaticNumber
import AFTD.Kb.Tcs.MatroidCommonListChromaticNumber
import AFTD.Kb.Tcs.MatroidStronglyBaseOrderable
import AFTD.Kb.Tcs.MatroidCommonColorable
import AFTD.Kb.Tcs.MatroidCommonListColorable

/-!
# matroid_sbo_common_list_chromatic_eq_of_le_two

Topic: combinatorics   Node: 12c5c4cbcd90

Provenance: formalization of a published result. Source: arXiv:2610.07318 (A note on the list chromatic number of two matroids), Corollary 2.3 ("in particular": χ = 2 implies χ_ℓ = 2), stated here with the chromatic numbers and including the cases χ = 0 and χ = 1; the paper's step through the 1976 common-chromatic-number theorem is not needed, since a common 2-coloring 2-colors each matroid.

For two loopless strongly base-orderable matroids on a common finite ground set whose common chromatic number is at most 2, the common list chromatic number equals the common chromatic number: χ(M₁, M₂) ≤ 2 implies χ_ℓ(M₁, M₂) = χ(M₁, M₂). This settles the open question χ_ℓ = χ for strongly base-orderable pairs in all cases with χ ≤ 2.
-/

theorem matroid_sbo_common_list_chromatic_eq_of_le_two {α : Type*} (M₁ M₂ : Matroid α)
    [M₁.Finite] (h₁ : M₁.Loopless) (h₂ : M₂.Loopless) (hE : M₁.E = M₂.E)
    (hs₁ : matroid_strongly_base_orderable M₁) (hs₂ : matroid_strongly_base_orderable M₂)
    (h : matroid_common_chromatic_number M₁ M₂ ≤ 2) :
    matroid_common_list_chromatic_number M₁ M₂ = matroid_common_chromatic_number M₁ M₂ := by
  refine le_antisymm ?_ (matroid_common_chromatic_le_list_chromatic M₁ M₂ h₁ h₂ hE)
  have hne : {k | matroid_common_colorable M₁ M₂ k}.Nonempty :=
    ⟨_, matroid_common_colorable_of_list_colorable M₁ M₂ _
      (matroid_common_list_colorable_of_ncard_le M₁ M₂ h₁ h₂ hE _ le_rfl)⟩
  have hmem : matroid_common_colorable M₁ M₂ (matroid_common_chromatic_number M₁ M₂) :=
    Nat.sInf_mem hne
  have key : matroid_common_list_colorable M₁ M₂ (matroid_common_chromatic_number M₁ M₂) := by
    generalize matroid_common_chromatic_number M₁ M₂ = χ at h hmem ⊢
    interval_cases χ
    · obtain ⟨c, hc, hind⟩ := hmem
      exact fun L _ => ⟨c, fun e he => absurd (hc e he) (Nat.not_lt_zero _), hind⟩
    · exact matroid_common_list_colorable_one_of_colorable_one M₁ M₂ hmem
    · exact matroid_sbo_common_list_colorable_two_of_common_colorable_two M₁ M₂ hE hs₁ hs₂ hmem
  exact Nat.sInf_le key
