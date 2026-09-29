import AFTD.Prelude
import AFTD.Kb.Tcs.CoClass
import AFTD.Kb.Tcs.ClassClosedUnderComplIffEqCo

/-!
# decider_class_eq_co

Topic: complexity_basics   Node: a190602468d3

Any complexity class defined by a family of deciders that is closed under negation equals its complement class.
-/

/-- A deterministic complexity class defined by deciders closed under negation equals its complement class. -/
theorem decider_class_eq_co {α : Type*} (D : (List α → Bool) → Prop)
    (hD : ∀ f, D f → D (fun w => !f w)) :
    ∀ L : Language α, (∃ f, D f ∧ ∀ w, w ∈ L ↔ f w = true) ↔
      CoClass (fun L' : Language α => ∃ f, D f ∧ ∀ w, w ∈ L' ↔ f w = true) L := by
  let C : Language α → Prop := fun L' => ∃ f, D f ∧ ∀ w, w ∈ L' ↔ f w = true
  have h_compl : ∀ L, C L → C Lᶜ := by
    intro L ⟨f, hfD, hfL⟩
    refine ⟨fun w => !f w, hD f hfD, ?_⟩
    intro w
    change (w ∉ L) ↔ (!f w) = true
    rw [hfL w]
    cases f w <;> simp
  exact (class_closed_under_compl_iff_eq_co C).mp h_compl
