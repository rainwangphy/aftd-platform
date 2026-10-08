import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidSboListColorableTwoOfColorableTwo
import AFTD.Kb.Tcs.MatroidStronglyBaseOrderable
import AFTD.Kb.Tcs.MatroidCommonColorable
import AFTD.Kb.Tcs.MatroidCommonListColorable

/-!
# matroid_sbo_common_list_colorable_two_of_common_colorable_two

Topic: combinatorics   Node: 6b643fff85eb

Provenance: formalization of a published result. Source: arXiv:2610.07318 (A note on the list chromatic number of two matroids), Corollary 2.3 ("in particular" part). The paper derives it through the 1976 theorem on common chromatic numbers of strongly base-orderable matroids; here it follows directly from the first part, since a common 2-coloring 2-colors each matroid.

If two strongly base-orderable matroids on a common finite ground set have a common coloring with two colors, then they are 2-list-colorable in common. This is the case χ(M₁, M₂) ≤ 2 of the open question whether χ_ℓ = χ for strongly base-orderable pairs.
-/

theorem matroid_sbo_common_list_colorable_two_of_common_colorable_two {α : Type*}
    (M₁ M₂ : Matroid α) [M₁.Finite] (hE : M₁.E = M₂.E)
    (h₁ : matroid_strongly_base_orderable M₁) (h₂ : matroid_strongly_base_orderable M₂)
    (h : matroid_common_colorable M₁ M₂ 2) : matroid_common_list_colorable M₁ M₂ 2 := by
  obtain ⟨c, hc, hind⟩ := h
  refine matroid_sbo_list_colorable_two_of_colorable_two M₁ M₂ hE h₁ h₂
    ⟨c, hc, fun γ => ⟨(hind γ).1, (hind γ).1⟩⟩ ⟨c, hE ▸ hc, fun γ => ?_⟩
  have hs : {e | e ∈ M₂.E ∧ c e = γ} = {e | e ∈ M₁.E ∧ c e = γ} := by rw [hE]
  rw [hs]
  exact ⟨(hind γ).2, (hind γ).2⟩
