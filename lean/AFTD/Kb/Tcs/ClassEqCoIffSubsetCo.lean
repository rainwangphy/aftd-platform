import AFTD.Prelude
import AFTD.Kb.Tcs.CoClass

/-!
# class_eq_co_iff_subset_co

Topic: complexity_basics   Node: 9422a0d4583e

A complexity class equals its complement class if and only if it is contained in its complement class.
-/

/-- A class equals its complement class iff it is contained in its complement class. -/
theorem class_eq_co_iff_subset_co {α : Type*} (C : Language α → Prop) :
    (∀ L, C L ↔ CoClass C L) ↔ (∀ L, C L → CoClass C L) := by
  constructor
  · intro h L
    exact (h L).1
  · intro h L
    constructor
    · exact h L
    · intro hL
      have h1 := h Lᶜ hL
      dsimp [CoClass] at h1
      rwa [compl_compl] at h1
