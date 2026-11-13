import AFTD.Prelude

/-!
# graph_state_fisher_q

Topic: quantum_mechanics   Node: 22c00b55242c

Provenance: formalization of a published result. Source: arXiv:2611.08593, Eqs. (9)-(10)

For any finite simple graph G on vertex set V, the collective-X quantum Fisher information Q(G) is the sum over all ordered pairs (u, v) in V of the indicator that u and v have identical open neighborhoods.
-/

/-- Collective-X quantum Fisher information of a graph state G, given by the sum of indicators of open-neighborhood equality over ordered vertex pairs. -/
noncomputable def graph_state_fisher_q {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := by
  classical
  exact ∑ u : V, ∑ v : V, if G.neighborSet u = G.neighborSet v then (1 : ℕ) else 0
