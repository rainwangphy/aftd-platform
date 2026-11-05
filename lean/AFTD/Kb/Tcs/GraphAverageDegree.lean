import AFTD.Prelude

/-!
# graph_average_degree

Topic: graphs   Node: 992b267c20da

Provenance: formalization of a published result. Source: arXiv:2611.05034

The average degree of a finite simple graph G is the real number 2 * |E(G)| / |V(G)|.
-/

open scoped Classical in
/-- The average degree of a finite simple graph G, defined as the real number 2 * |E(G)| / |V(G)|. -/
noncomputable def graph_average_degree {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ := (2 * G.edgeFinset.card : ℝ) / Fintype.card V
