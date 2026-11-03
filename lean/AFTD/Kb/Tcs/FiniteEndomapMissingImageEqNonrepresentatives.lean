import AFTD.Prelude

/-!
# finite_endomap_missing_image_eq_nonrepresentatives

Topic: combinatorics   Node: 95adf2dfa012

Provenance: helper lemma. Collision counting for the small-overlap route to OP-110.

For a finite endomap with a chosen representative from each nonempty fiber, the number of elements outside its image equals the number of nonrepresentatives.
-/

theorem finite_endomap_missing_image_eq_nonrepresentatives
    (α : Type) [Fintype α] [DecidableEq α] (f r : α → α)
    (hr : ∀ x, f (r (f x)) = f x) :
    ((Finset.univ : Finset α) \ Finset.univ.image f).card =
      ((Finset.univ : Finset α).filter (fun x => r (f x) ≠ x)).card := by
  have h_bij : (Finset.univ.image f).card = (Finset.univ.filter (fun x => r (f x) = x)).card := by
    apply Finset.card_bij (fun y _ => r y)
    · intro y hy
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy
      rcases hy with ⟨x, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact congr_arg r (hr x)
    · intro y₁ hy₁ y₂ hy₂ h_eq
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy₁ hy₂
      rcases hy₁ with ⟨x₁, rfl⟩
      rcases hy₂ with ⟨x₂, rfl⟩
      rw [← hr x₁, ← hr x₂, h_eq]
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact ⟨f x, Finset.mem_image_of_mem f (Finset.mem_univ x), hx⟩
  rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_sdiff_of_subset (Finset.subset_univ _), h_bij]
