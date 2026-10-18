import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidCommonListColorable

/-!
# matroid_common_list_colorable_of_reduction

Topic: combinatorics   Node: 3ff86e9e7147

Provenance: helper lemma. step towards matroid_sbo_common_list_chromatic_eq

If N₁ is a reduction of M₁ (every N₁-independent set is M₁-independent, on the same ground set) and N₂ is a reduction of M₂, then k-list-colourability of the pair (N₁, N₂) implies k-list-colourability of (M₁, M₂).
-/

/-- List-colourability passes from a pair of reductions to the pair being reduced. -/
theorem matroid_common_list_colorable_of_reduction {α : Type*} (M₁ M₂ N₁ N₂ : Matroid α) (k : ℕ)
    (hEN : N₁.E = M₁.E)
    (h₁ : ∀ T : Set α, N₁.Indep T → M₁.Indep T) (h₂ : ∀ T : Set α, N₂.Indep T → M₂.Indep T)
    (h : matroid_common_list_colorable N₁ N₂ k) : matroid_common_list_colorable M₁ M₂ k := by
  intro L hL
  have hL' : ∀ e ∈ N₁.E, k ≤ (L e).card := by
    intro e he; exact hL e (hEN ▸ he)
  obtain ⟨c, hc, hind⟩ := h L hL'
  refine ⟨c, ?_, ?_⟩
  · intro e he; exact hc e (hEN ▸ he)
  · intro γ
    have hset : {e : α | e ∈ M₁.E ∧ c e = γ} = {e : α | e ∈ N₁.E ∧ c e = γ} := by
      ext e; rw [hEN]
    rw [hset]
    exact ⟨h₁ _ (hind γ).1, h₂ _ (hind γ).2⟩
