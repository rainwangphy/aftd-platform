import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphOfEdgeList
import AFTD.Kb.Tcs.SimpleGraphIsTriangleDistinct
import AFTD.Kb.Tcs.SimpleGraphOfEdgeListDecidableRel
import AFTD.Kb.Tcs.SimpleGraphIsTriangleDistinctDecidable

/-!
# eight_regular_triangle_distinct_certificate

Topic: graphs   Node: 89d56e4af6b2

Provenance: helper lemma. step towards regular_eight_triangle_distinct_witness

A computable boolean certificate checker for the regularity-8 witness problem: it returns true exactly when every one of the n vertices {0,…,n−1} has exactly 8 neighbours in the graph of the edge list L and the vertex triangle-degrees of that graph are pairwise distinct.
-/

/-- Computable checker: is the graph of this edge list 8-regular with pairwise distinct vertex triangle-degrees? -/
def eight_regular_triangle_distinct_certificate {n : ℕ} (L : List (Fin n × Fin n)) : Bool := ((List.finRange n).all (fun v => ((simple_graph_of_edge_list L).neighborFinset v).card == 8)) &&
    decide (simple_graph_is_triangle_distinct (simple_graph_of_edge_list L))
