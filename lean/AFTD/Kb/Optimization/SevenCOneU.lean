import AFTD.Prelude
import AFTD.Kb.Optimization.SevenArc
import AFTD.Kb.Optimization.SevenCost
import AFTD.Kb.Optimization.SevenUnsplittableLoad
import AFTD.Kb.Optimization.SevenIsOneAdmissible

/-!
# seven_c_one_u

Topic: submodular   Node: b68ab32d5007

Provenance: formalization of a published result. Source: arXiv:2611.23244 Equation (7)

The minimum routing cost c_1^u(f; l) attainable by an unsplittable flow that is 1-admissible relative to f under unit arc-cost vector l, defined as the infimum of the costs of 1-admissible unsplittable selections.
-/

/-- Minimum routing cost over all 1-admissible unsplittable flows under unit arc costs. -/
noncomputable def seven_c_one_u (d1 d2 d3 a b c : ℝ) (l : SevenArc → ℝ) : ℝ := sInf { seven_cost (seven_unsplittable_load d1 d2 d3 y1 y2 y3) l |
    (y1 : Bool) (y2 : Bool) (y3 : Bool) (_ : seven_is_one_admissible d1 d2 d3 a b c y1 y2 y3) }
