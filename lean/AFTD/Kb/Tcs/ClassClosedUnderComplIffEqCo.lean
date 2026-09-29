import AFTD.Prelude
import AFTD.Kb.Tcs.CoClass

/-!
# class_closed_under_compl_iff_eq_co

Topic: complexity_basics   Node: 0323d70284d1

A complexity class C is closed under complement if and only if C equals its complement class co(C).
-/

/-- A complexity class is closed under complement if and only if it equals its co-class. -/
theorem class_closed_under_compl_iff_eq_co {α : Type*} (C : Language α → Prop) :
    (∀ L, C L → C Lᶜ) ↔ (∀ L, C L ↔ CoClass C L) := by
  constructor
  · intro h L
    refine ⟨h L, fun hCo => ?_⟩
    have h1 := h Lᶜ hCo
    rwa [compl_compl] at h1
  · intro h L hCL
    exact (h L).mp hCL
