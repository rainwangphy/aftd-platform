import AFTD.Prelude
import AFTD.Kb.Tcs.GraphIsDImmune

/-!
# graph_d_immune_min_edges

Topic: graphs   Node: 374d40d04114

Provenance: formalization of a published result. Source: arXiv:2611.26556 Section 1

The quantity mu_d(n) is the minimum number of edges among all d-immune simple graphs on n vertices.
-/

/-- The minimum number of edges mu_d(n) of a d-immune simple graph on n vertices. -/
noncomputable def graph_d_immune_min_edges (d n : ℕ) : ℕ :=
  open scoped Classical in
  sInf { m : ℕ | ∃ G : SimpleGraph (Fin n), graph_is_d_immune G d ∧ G.edgeFinset.card = m }
