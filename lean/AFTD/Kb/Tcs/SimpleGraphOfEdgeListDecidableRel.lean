import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphOfEdgeList

/-!
# simple_graph_of_edge_list_decidable_rel

Topic: graphs   Node: 3e1a12e83c49

Provenance: helper lemma. step towards exists_nonempty_regular_eight_triangle_distinct

Adjacency in the graph determined by an edge list is decidable.
-/

/-- Adjacency of a graph given by an edge list is decidable, so its triangle-degrees compute. -/
instance simple_graph_of_edge_list_decidable_rel {n : ℕ} (L : List (Fin n × Fin n)) :
    DecidableRel (simple_graph_of_edge_list L).Adj := inferInstanceAs (DecidableRel (SimpleGraph.fromRel (fun a b : Fin n => (a, b) ∈ L)).Adj)
