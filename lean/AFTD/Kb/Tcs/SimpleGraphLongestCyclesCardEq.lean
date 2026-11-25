import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsLongestCycle
import AFTD.Kb.Tcs.SimpleGraphIsCycleSubgraph

/-!
# simple_graph_longest_cycles_card_eq

Topic: graphs   Node: abade2ae062f

Provenance: helper lemma. step towards k_connected_longest_cycles_intersection_bound

Any two longest cycles of a simple graph have the same number of vertices.
-/

/-- Any two longest cycles of a simple graph have the same vertex cardinality. -/
theorem simple_graph_longest_cycles_card_eq {V : Type*} {G : SimpleGraph V} (C D : G.Subgraph) (hC : simple_graph_is_longest_cycle C) (hD : simple_graph_is_longest_cycle D) : C.verts.ncard = D.verts.ncard := by
  exact le_antisymm (hD.2 C hC.1) (hC.2 D hD.1)
