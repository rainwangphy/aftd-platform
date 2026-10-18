import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidCommonListColorable

/-!
# matroid_common_list_colorable_mono

Topic: combinatorics   Node: b7f90956fd1c

Provenance: helper lemma. step towards matroid_sbo_common_list_chromatic_eq

If a pair of matroids is k-list-colourable then it is k'-list-colourable for every k' ≥ k: lists that are at least as long are only easier to satisfy, with the same colouring as witness.
-/

/-- k-list-colourability of a pair of matroids is monotone in k. -/
theorem matroid_common_list_colorable_mono {α : Type*} (M₁ M₂ : Matroid α) {k k' : ℕ}
    (hkk : k ≤ k') (h : matroid_common_list_colorable M₁ M₂ k) :
    matroid_common_list_colorable M₁ M₂ k' := by
  intro L hL
  exact h L (fun e he => le_trans hkk (hL e he))
