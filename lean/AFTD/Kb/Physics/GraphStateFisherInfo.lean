import AFTD.Prelude

/-!
# graph_state_fisher_info

Topic: quantum_mechanics   Node: 29928ceeb0ae

Provenance: formalization of a published result. Source: arXiv:2411.08593, Eqs. (9)-(10)

For a finite simple graph G on vertex type V with decidable equality and adjacency, the collective-X quantum Fisher information graph_state_fisher_info G is the number of pairs (u, v) in V × V such that the open neighborhoods of u and v are equal.
-/

/-- The collective-X quantum Fisher information Q(G) of a graph state, equal to the number of pairs of vertices with equal open neighborhoods. -/
def graph_state_fisher_info {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ := ((Finset.univ ×ˢ Finset.univ).filter (fun (u, v) => G.neighborFinset u = G.neighborFinset v)).card
