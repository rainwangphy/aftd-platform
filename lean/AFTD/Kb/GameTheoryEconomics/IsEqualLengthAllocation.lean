import AFTD.Prelude

/-!
# is_equal_length_allocation

Topic: fair_division   Node: 7e8db9744992

Provenance: formalization of a published result. Source: arXiv:2610.19733 Section 2

An allocation is equal-length if each bundle has Lebesgue measure equal to `1 / n`.
-/

/-- An allocation is equal-length if each agent's bundle has Lebesgue measure `1 / n`. -/
def is_equal_length_allocation (n : ℕ) (C : Fin n → Set ℝ) : Prop :=
  ∀ i : Fin n, MeasureTheory.volume (C i) = ENNReal.ofReal (1 / (n : ℝ))
