import AFTD.Prelude
import AFTD.Kb.Tcs.Multigraph
import AFTD.Kb.Tcs.MultigraphIsProperEdgeColoring

/-!
# multigraph_chromatic_index

Topic: graphs   Node: 8fb6eac4f7c8

Provenance: formalization of a published result. Source: scout/2611-29111-when-do-local-bounds-permit-optimal-edge-colorings.md:84

The chromatic index chi'(G) of a multigraph G is the minimum number of colors in a proper edge-coloring of G.
-/

/-- The chromatic index chi'(G) of a multigraph G. -/
noncomputable def multigraph_chromatic_index {V : Type*} (G : Multigraph V) : ℕ := sInf {k : ℕ | ∃ c : V → V → Finset ℕ, multigraph_is_proper_edge_coloring G k c}
