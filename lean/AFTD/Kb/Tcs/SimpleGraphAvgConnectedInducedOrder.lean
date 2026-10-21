import AFTD.Prelude

/-!
# simple_graph_avg_connected_induced_order

Topic: graphs   Node: 8910f617a97f

Provenance: formalization of a published result. Source: arXiv:2610.27553 (A proof of Vince's conjecture on the average order of connected induced subgraphs), Sec. 1, definition of A(G)

A(G) = (Σ |S|)/N, the sum over the N vertex sets S ⊆ V(G) whose induced subgraph G[S] is connected (and nonempty).
-/

/-- A(G): the average order of the connected induced subgraphs of G, i.e. the mean of |S| over the vertex sets S inducing a connected subgraph (connected includes nonempty). -/
noncomputable def simple_graph_avg_connected_induced_order {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℚ := by
  classical exact
    (((Finset.univ.filter (fun S : Finset V => (G.induce (S : Set V)).Connected)).sum
        Finset.card : ℕ) : ℚ) /
      (Finset.univ.filter (fun S : Finset V => (G.induce (S : Set V)).Connected)).card
