import AFTD.Prelude
import AFTD.Kb.Tcs.IsMutualVisibilitySet
import AFTD.Kb.Tcs.SimpleGraphPowerOne

/-!
# is_mutual_visibility_set_empty

Topic: graphs   Node: 2e0d3abaccc2

Provenance: helper lemma. arXiv:2611.09513, Section 1

The empty set of vertices in any simple graph G is a mutual-visibility set.
-/

/-- The empty set is a mutual-visibility set. -/
theorem is_mutual_visibility_set_empty {V : Type*} (G : SimpleGraph V) :
    is_mutual_visibility_set G ∅ := by first | exact simple_graph_power_one | (apply simple_graph_power_one <;> assumption) | (apply simple_graph_power_one <;> simp_all) | simpa using simple_graph_power_one | (simp only [is_mutual_visibility_set] at *; first | exact simple_graph_power_one | (apply simple_graph_power_one <;> assumption) | (apply simple_graph_power_one <;> simp_all) | simpa using simple_graph_power_one)
