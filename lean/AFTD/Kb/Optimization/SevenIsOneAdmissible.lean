import AFTD.Prelude
import AFTD.Kb.Optimization.SevenArc
import AFTD.Kb.Optimization.SevenFractionalLoad
import AFTD.Kb.Optimization.SevenUnsplittableLoad

/-!
# seven_is_one_admissible

Topic: submodular   Node: a0461f8612ff

Provenance: formalization of a published result. Source: arXiv:2611.23244 Definition 2.2

An unsplittable selection y_1, y_2, y_3 is 1-admissible relative to fractional flow parameters a, b, c and demands d_1, d_2, d_3 if the unsplittable load on every arc is at most the fractional load plus D, where D = max{d_1, max{d_2, d_3}}.
-/

/-- Predicate that an unsplittable selection is 1-admissible relative to a fractional reference flow. -/
def seven_is_one_admissible (d1 d2 d3 a b c : ℝ) (y1 y2 y3 : Bool) : Prop := let D := max d1 (max d2 d3)
  ∀ e : SevenArc, seven_unsplittable_load d1 d2 d3 y1 y2 y3 e ≤ seven_fractional_load d1 d2 d3 a b c e + D
