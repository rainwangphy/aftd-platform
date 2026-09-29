import AFTD.Prelude
import AFTD.Kb.Tcs.CoClass

/-!
# co_class_monotone

Topic: complexity_basics   Node: bdc460c22b60

If a complexity class C₁ is contained in a complexity class C₂, then co(C₁) is contained in co(C₂).
-/

/-- The co-class operation preserves class inclusion. -/
theorem co_class_monotone {α : Type*} (C₁ C₂ : Language α → Prop)
    (h : ∀ L, C₁ L → C₂ L) (L : Language α) (hL : CoClass C₁ L) : CoClass C₂ L := h Lᶜ hL
