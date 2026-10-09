import AFTD.Prelude

/-!
# three_graph_link

Topic: combinatorics   Node: 6b95923df829

Provenance: formalization of a published result. Source: arXiv:2610.11642 (A counterexample to the bipartite-link conjecture for 3-graphs), Sec. 1 (vertex link graph ∂_i F of a 3-graph).

The link graph of a vertex i in a 3-uniform hypergraph F: two distinct vertices j, k are adjacent iff {i, j, k} is an edge of F.
-/

/-- The link graph of the vertex `i` in a 3-uniform hypergraph `F` (a family of 3-sets): distinct `j, k` are adjacent iff `{i, j, k} ∈ F`. -/
def three_graph_link {V : Type*} [DecidableEq V] (F : Finset (Finset V)) (i : V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun j k => ({i, j, k} : Finset V) ∈ F)
