import AFTD.Prelude
import AFTD.Kb.Tcs.IsLinearForest
import AFTD.Kb.Tcs.SimpleGraphPowerOne

/-!
# is_linear_forest_bot

Topic: graphs   Node: d8da45a02722

Provenance: helper lemma. folklore

The empty simple graph on any vertex type is a linear forest.
-/

/-- The empty simple graph on any vertex type is a linear forest. -/
theorem is_linear_forest_bot {V : Type*} : is_linear_forest (⊥ : SimpleGraph V) := by first | exact simple_graph_power_one | (apply simple_graph_power_one <;> assumption) | (apply simple_graph_power_one <;> simp_all) | simpa using simple_graph_power_one | (simp only [is_linear_forest] at *; first | exact simple_graph_power_one | (apply simple_graph_power_one <;> assumption) | (apply simple_graph_power_one <;> simp_all) | simpa using simple_graph_power_one)
