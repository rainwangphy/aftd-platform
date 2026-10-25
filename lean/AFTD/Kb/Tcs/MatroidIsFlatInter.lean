import AFTD.Prelude

/-!
# matroid_isFlat_inter

Topic: graphs   Node: 44555210ee07

Provenance: helper lemma. Mathlib.Combinatorics.Matroid.Closure

In any matroid M, if F₁ and F₂ are flats of M, then their intersection F₁ ∩ F₂ is also a flat of M.
-/

/-- The intersection of two flats in a matroid is a flat. -/
theorem matroid_isFlat_inter {α : Type*} (M : Matroid α) {F₁ F₂ : Set α}
    (h₁ : M.IsFlat F₁) (h₂ : M.IsFlat F₂) : M.IsFlat (F₁ ∩ F₂) := by
  have h := Matroid.IsFlat.iInter (ι := Bool) (Fs := fun b => bif b then F₁ else F₂)
    (fun b => by cases b <;> assumption)
  have heq : (⋂ i, (bif i then F₁ else F₂ : Set α)) = F₁ ∩ F₂ := by
    ext x
    simp [and_comm]
  simpa [heq] using h
