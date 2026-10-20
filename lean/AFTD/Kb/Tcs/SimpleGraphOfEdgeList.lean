import AFTD.Prelude

/-!
# simple_graph_of_edge_list

Topic: graphs   Node: b0567cc984dd

Provenance: helper lemma. step towards exists_nonempty_regular_eight_triangle_distinct

The simple graph on {0,…,n−1} whose edges are the unordered pairs occurring in the list L (a pair (a, b) in L contributes the edge {a, b}, and a pair (a, a) contributes nothing).
-/

/-- Graph on `Fin n` built from a list of ordered vertex pairs, symmetrized and made irreflexive by `SimpleGraph.fromRel`. -/
def simple_graph_of_edge_list {n : ℕ} (L : List (Fin n × Fin n)) : SimpleGraph (Fin n) := SimpleGraph.fromRel fun a b => (a, b) ∈ L
