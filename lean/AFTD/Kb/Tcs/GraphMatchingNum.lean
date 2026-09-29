import AFTD.Prelude

/-!
# graph_matching_num

Topic: graphs   Node: 711dbd073ac0

The matching number of a graph G is the supremum of the cardinalities of the edge sets of all matchings in G.
-/

/-- The matching number of a graph, defined as the supremum of cardinalities of edge sets of matchings in G. -/
noncomputable def graph_matching_num {V : Type*} (G : SimpleGraph V) : ℕ∞ := ⨆ (M : SimpleGraph.Subgraph G) (_ : M.IsMatching), M.edgeSet.encard
