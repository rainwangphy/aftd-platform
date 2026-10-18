import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidCommonListColorableListChromaticNumber
import AFTD.Kb.Tcs.MatroidCommonListColorableMono
import AFTD.Kb.Tcs.MatroidCommonListColorableOfNcardLe
import AFTD.Kb.Tcs.MatroidCommonListChromaticNumber
import AFTD.Kb.Tcs.MatroidCommonListColorable

/-!
# matroid_common_list_chromatic_le_iff

Topic: combinatorics   Node: 5a69e3a13e93

Provenance: helper lemma. step towards matroid_common_list_chromatic_le_add_const

For two loopless matroids on a common finite ground set, the common list chromatic number is at most k if and only if the pair is k-list-colorable: χ_ℓ(M₁, M₂) ≤ k ↔ matroid_common_list_colorable M₁ M₂ k. This is the exact dictionary between a numeric bound on χ_ℓ and the list-colorability predicate used throughout the additive-gap argument.
-/

/-- χ_ℓ(M₁,M₂) ≤ k iff the pair is k-list-colorable. -/
theorem matroid_common_list_chromatic_le_iff {α : Type*} (M₁ M₂ : Matroid α) [Finite α] (h₁ : M₁.Loopless) (h₂ : M₂.Loopless) (hE : M₁.E = M₂.E) (k : ℕ) :
    (matroid_common_list_chromatic_number M₁ M₂ ≤ k ↔ matroid_common_list_colorable M₁ M₂ k) := by
  constructor
  · intro h
    have hne : ({k | matroid_common_list_colorable M₁ M₂ k} : Set ℕ).Nonempty :=
      ⟨M₁.E.ncard, matroid_common_list_colorable_of_ncard_le M₁ M₂ h₁ h₂ hE _ le_rfl⟩
    have hmem := Nat.sInf_mem hne
    exact matroid_common_list_colorable_mono M₁ M₂ h hmem
  · intro h
    exact Nat.sInf_le h
