import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidStronglyBaseOrderable

/-!
# matroid_strongly_base_orderable_freeOn

Topic: combinatorics   Node: 76d5112a1195

Provenance: helper lemma. sanity check of matroid_strongly_base_orderable

A free matroid (every subset of the ground set independent) is strongly base-orderable.
-/

theorem matroid_strongly_base_orderable_freeOn {α : Type*} (E : Set α) :
    matroid_strongly_base_orderable (Matroid.freeOn E) := by
  intro B₁ B₂ h₁ h₂
  rw [Matroid.freeOn_isBase_iff] at h₁ h₂
  subst h₁; subst h₂
  refine ⟨Equiv.refl _, fun X => ?_⟩
  rw [Matroid.freeOn_isBase_iff]
  ext x; constructor
  · rintro (⟨hx, -⟩ | ⟨y, -, rfl⟩)
    · exact hx
    · exact y.2
  · intro hx
    by_cases h : x ∈ ((↑) '' X : Set α)
    · obtain ⟨y, hy, rfl⟩ := h
      exact Or.inr ⟨y, hy, rfl⟩
    · exact Or.inl ⟨hx, h⟩
