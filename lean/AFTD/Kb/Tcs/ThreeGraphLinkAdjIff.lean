import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeGraphLink

/-!
# three_graph_link_adj_iff

Topic: combinatorics   Node: 4f942b253692

Provenance: helper lemma. Sanity check of the definitions of arXiv:2610.11642 (A counterexample to the bipartite-link conjecture for 3-graphs). Unfolds the link graph.

In the link graph of i, j and k are adjacent iff they are distinct and {i, j, k} (in either order of j, k) is an edge.
-/

theorem three_graph_link_adj_iff {V : Type*} [DecidableEq V] (F : Finset (Finset V)) (i j k : V) :
    (three_graph_link F i).Adj j k ↔ j ≠ k ∧ (({i, j, k} : Finset V) ∈ F ∨ ({i, k, j} : Finset V) ∈ F) := by
  simp [three_graph_link, SimpleGraph.fromRel_adj]
