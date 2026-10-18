import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidCommonListColorable

/-!
# matroid_common_list_colorable_iff_lists_card_eq

Topic: combinatorics   Node: fbd8ef61da90

Provenance: helper lemma. step towards matroid_sbo_common_list_chromatic_eq

A pair of matroids is k-list-colourable if and only if it has an L-colouring for every list assignment whose lists have cardinality exactly k on the ground set (rather than at least k).
-/

/-- Exact-size lists suffice for testing k-list-colourability. -/
theorem matroid_common_list_colorable_iff_lists_card_eq {α : Type*} (M₁ M₂ : Matroid α) (k : ℕ) :
    matroid_common_list_colorable M₁ M₂ k ↔
      ∀ (L : α → Finset ℕ), (∀ e ∈ M₁.E, (L e).card = k) →
        ∃ c : α → ℕ, (∀ e ∈ M₁.E, c e ∈ L e) ∧
          ∀ γ : ℕ, M₁.Indep {e | e ∈ M₁.E ∧ c e = γ} ∧ M₂.Indep {e | e ∈ M₁.E ∧ c e = γ} := by
  constructor
  · intro h L hL
    apply h L
    intro e he
    rw [hL e he]
  · intro h L hL
    have h_sub : ∀ e, ∃ (t : Finset ℕ), e ∈ M₁.E → t ⊆ L e ∧ t.card = k := by
      intro e
      by_cases he : e ∈ M₁.E
      · obtain ⟨t, ht, hcard⟩ := Finset.exists_subset_card_eq (hL e he)
        exact ⟨t, fun _ => ⟨ht, hcard⟩⟩
      · exact ⟨∅, fun he' => False.elim (he he')⟩
    choose L' hL' using h_sub
    obtain ⟨c, hc, hindep⟩ := h L' (fun e he => (hL' e he).2)
    exact ⟨c, fun e he => (hL' e he).1 (hc e he), hindep⟩
