import AFTD.Prelude
import AFTD.Kb.Tcs.Zycle
import AFTD.Kb.Tcs.IsThreeUniform

/-!
# op_1453_zycle_four_three_uniform

Topic: combinatorics   Node: e0a666d0cacb

Provenance: formalization of a published result. Source: arXiv:2611.12582 Section 1

The 4-zycle Z₄ is a 3-uniform hypergraph, meaning every hyperedge has cardinality 3.
-/

/-- The 4-zycle Z₄ is 3-uniform. -/
theorem op_1453_zycle_four_three_uniform : is_three_uniform (zycle 4) := by
  unfold is_three_uniform
  decide
