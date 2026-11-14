import AFTD.Prelude
import AFTD.Kb.Tcs.IsTwoKTwoFree
import AFTD.Kb.Tcs.SimpleGraphPowerOne

/-!
# bot_isTwoKTwoFree

Topic: graphs   Node: 697be3eea993

Provenance: helper lemma. arXiv:2611.17183, Definition 2.1

The empty graph on any vertex type is 2K₂-free.
-/

/-- The empty graph is 2K₂-free. -/
theorem bot_isTwoKTwoFree (V : Type*) : IsTwoKTwoFree (⊥ : SimpleGraph V) := by first | exact simple_graph_power_one | (apply simple_graph_power_one <;> assumption) | (apply simple_graph_power_one <;> simp_all) | simpa using simple_graph_power_one | (simp only [IsTwoKTwoFree] at *; first | exact simple_graph_power_one | (apply simple_graph_power_one <;> assumption) | (apply simple_graph_power_one <;> simp_all) | simpa using simple_graph_power_one)
