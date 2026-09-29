import AFTD.Prelude
import AFTD.Kb.Tcs.CoClass

/-!
# class_eq_co_of_class_eq

Topic: complexity_basics   Node: 393e0cc1dce3

If two complexity classes are equal and the first equals its complement class, then the second equals its complement class too.
-/

/-- Equalling one's complement class transfers along equality of classes. -/
theorem class_eq_co_of_class_eq {α : Type*} (C₁ C₂ : Language α → Prop)
    (h₁ : ∀ L, C₁ L ↔ CoClass C₁ L)
    (h₂ : ∀ L, C₁ L ↔ C₂ L) :
    ∀ L, C₂ L ↔ CoClass C₂ L := by
  intro L
  unfold CoClass at *
  rw [← h₂, h₁, h₂]
