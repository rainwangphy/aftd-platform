import AFTD.Prelude
import AFTD.Kb.Tcs.IsGraphBisection

/-!
# is_graph_bisection_singleton_bool

Topic: graphs   Node: 762e8d02fcef

Provenance: helper lemma. folklore

In the two-element type Bool, the singleton subset {true} is a bisection.
-/

/-- The singleton {true} in Bool is a bisection. -/
theorem is_graph_bisection_singleton_bool : is_graph_bisection ({true} : Finset Bool) := by
  simp [is_graph_bisection, Finset.card_compl]
