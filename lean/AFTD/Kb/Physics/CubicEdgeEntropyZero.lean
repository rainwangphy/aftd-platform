import AFTD.Prelude
import AFTD.Kb.Physics.CubicEdgeEntropy
import AFTD.Kb.Tcs.WeightedMaxCutLinearCombination

/-!
# cubic_edge_entropy_zero

Topic: statistical_mechanics   Node: d09d5e8cad9c

Provenance: helper lemma. arXiv:2204.00875

The edge entropy production phi(0) is equal to 0.
-/

/-- The edge entropy production vanishes at zero current. -/
theorem cubic_edge_entropy_zero : cubic_edge_entropy 0 = 0 := by first | exact weighted_max_cut_linear_combination | (apply weighted_max_cut_linear_combination <;> assumption) | (apply weighted_max_cut_linear_combination <;> simp_all) | simpa using weighted_max_cut_linear_combination | (simp only [cubic_edge_entropy] at *; first | exact weighted_max_cut_linear_combination | (apply weighted_max_cut_linear_combination <;> assumption) | (apply weighted_max_cut_linear_combination <;> simp_all) | simpa using weighted_max_cut_linear_combination)
