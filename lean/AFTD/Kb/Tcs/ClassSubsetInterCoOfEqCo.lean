import AFTD.Prelude
import AFTD.Kb.Tcs.CoClass
import AFTD.Kb.Tcs.CoClassMonotone

/-!
# class_subset_inter_co_of_eq_co

Topic: complexity_basics   Node: 4e7241877723

If a complexity class equals its complement class and is contained in a second class, then it is contained in the intersection of that second class with the second class's complement class.
-/

/-- A class closed under complement and contained in a second class is contained in that class intersected with its complement class. -/
theorem class_subset_inter_co_of_eq_co {α : Type*} (C₁ C₂ : Language α → Prop)
    (h₁ : ∀ L, C₁ L ↔ CoClass C₁ L)
    (h₂ : ∀ L, C₁ L → C₂ L) :
    ∀ L, C₁ L → C₂ L ∧ CoClass C₂ L := fun L hL => ⟨h₂ L hL, co_class_monotone C₁ C₂ h₂ L ((h₁ L).mp hL)⟩
