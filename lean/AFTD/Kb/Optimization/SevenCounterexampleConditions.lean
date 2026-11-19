import AFTD.Prelude

/-!
# seven_counterexample_conditions

Topic: submodular   Node: 6848ff88685f

Provenance: formalization of a published result. Source: arXiv:2611.23244 Equation (26)

The four conditions characterizing counterexample reference flows: d_1 + d_2 > a + b + D, d_1 + d_3 > a + b + c + D, d_2 + d_3 > b + c + D, and a/d_1 + b/d_2 + c/d_3 > 1, where D = max{d_1, d_2, d_3}.
-/

/-- The four conditions characterizing counterexample reference flows on the seven-vertex topology. -/
def seven_counterexample_conditions (d1 d2 d3 a b c : ℝ) : Prop := let D := max d1 (max d2 d3)
  d1 + d2 > a + b + D ∧
  d1 + d3 > a + b + c + D ∧
  d2 + d3 > b + c + D ∧
  a / d1 + b / d2 + c / d3 > 1
