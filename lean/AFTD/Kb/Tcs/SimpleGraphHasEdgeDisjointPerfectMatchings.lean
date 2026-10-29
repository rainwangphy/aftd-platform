import AFTD.Prelude

/-!
# simple_graph_has_edge_disjoint_perfect_matchings

Topic: graphs   Node: b1b9f576159a

Provenance: original. Related work: folklore

A simple graph G has at least k pairwise edge-disjoint perfect matchings if there exists an indexed family of k subgraphs of G, each of which is a perfect matching, whose edge sets are pairwise disjoint.
-/

/-- A simple graph G contains at least k pairwise edge-disjoint perfect matchings. -/
def simple_graph_has_edge_disjoint_perfect_matchings {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop := ∃ (M : Fin k → G.Subgraph), (∀ i, (M i).IsPerfectMatching) ∧ Pairwise (fun i j => Disjoint (M i).edgeSet (M j).edgeSet)
