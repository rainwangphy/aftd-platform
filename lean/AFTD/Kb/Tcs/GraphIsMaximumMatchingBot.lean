import AFTD.Prelude
import AFTD.Kb.Tcs.GraphIsMaximumMatching
import AFTD.Kb.Tcs.GraphMatchingNumBot
import AFTD.Kb.Tcs.GraphMatchingNum

/-!
# graph_is_maximum_matching_bot

Topic: approximation   Node: b06f20400ab9

Provenance: helper lemma. folklore

The empty subgraph is a maximum matching of the empty graph.
-/

/-- The empty subgraph is a maximum matching of the empty graph. -/
theorem graph_is_maximum_matching_bot {V : Type*} : graph_is_maximum_matching (⊥ : SimpleGraph V) ⊥ := by
  simp [graph_is_maximum_matching, graph_matching_num_bot, SimpleGraph.Subgraph.IsMatching]
