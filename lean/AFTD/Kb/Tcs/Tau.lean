import AFTD.Prelude
import AFTD.Kb.Tcs.MaxInducedLinearForest
import AFTD.Kb.Tcs.GraphVertexDistSum

/-!
# tau

Topic: graphs   Node: 3093cf7346b0

Provenance: formalization of a published result. Source: arXiv:2611.12781, Section 2, equation (169)

For a vertex u in a finite simple graph G on vertex type V, tau G u is the integer (max_induced_linear_forest G : ℤ) * ((Fintype.card V : ℤ) - 1) - 2 * (graph_vertex_dist_sum G u : ℤ).
-/

/-- The vertex tau invariant: L(G)(n-1) - 2 * w_G(u). -/
noncomputable def tau {V : Type*} [Fintype V] (G : SimpleGraph V) (u : V) : ℤ := (max_induced_linear_forest G : ℤ) * ((Fintype.card V : ℤ) - 1) - 2 * (graph_vertex_dist_sum G u : ℤ)
