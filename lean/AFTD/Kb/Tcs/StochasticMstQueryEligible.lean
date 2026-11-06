import AFTD.Prelude

/-!
# stochastic_mst_query_eligible

Topic: algorithms   Node: 60720c1e7dcc

Provenance: formalization of a published result. Source: arXiv:2610.40844 (Stochastic Minimum Spanning Tree Identification with Binary Weights), Sec. 2.1 and Lemma 2.2: the minor G_beta obtained by contracting 0-edges and deleting 1-edges; an edge is worth querying iff it is neither a loop nor a bridge of G_beta

For a simple graph G on a vertex type V, finite sets Z and D of edges (Finsets of Sym2 V: Z the edges queried with weight 0, which are contracted, D those queried with weight 1, which are deleted) and an edge e (an element of Sym2 V), e is eligible for a query when: e is an edge of G, e is not in Z, e is not in D, and writing e = s(u, v), the vertices u and v are not joined by a path in the graph whose edges are exactly the elements of Z (so e is not a loop of the minor G/Z minus D), but are joined by a path in G after deleting e and the edges of D (so e is not a bridge of that minor).
-/

def stochastic_mst_query_eligible {V : Type*} (G : SimpleGraph V) (Z D : Finset (Sym2 V))
    (e : Sym2 V) : Prop :=
  e ∈ G.edgeSet ∧ e ∉ Z ∧ e ∉ D ∧ ∃ u v : V, e = s(u, v) ∧
    ¬ (SimpleGraph.fromEdgeSet (↑Z : Set (Sym2 V))).Reachable u v ∧
    (G.deleteEdges (insert e (↑D : Set (Sym2 V)))).Reachable u v
