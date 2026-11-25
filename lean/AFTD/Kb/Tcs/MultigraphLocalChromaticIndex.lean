import AFTD.Prelude
import AFTD.Kb.Tcs.Multigraph
import AFTD.Kb.Tcs.MultigraphIsProperEdgeColoring
import AFTD.Kb.Tcs.MultigraphIsLocallyBounded

/-!
# multigraph_local_chromatic_index

Topic: graphs   Node: df61d30be1b1

Provenance: formalization of a published result. Source: scout/2611-29111-when-do-local-bounds-permit-optimal-edge-colorings.md:95

The local chromatic index chi'_loc(G) of a multigraph G is the minimum number of colors in a locally bounded proper edge-coloring of G.
-/

/-- The local chromatic index chi'_loc(G) of a multigraph G. -/
noncomputable def multigraph_local_chromatic_index {V : Type*} [Fintype V] (G : Multigraph V) : ℕ := sInf {k : ℕ | ∃ c : V → V → Finset ℕ, multigraph_is_proper_edge_coloring G k c ∧ multigraph_is_locally_bounded G c}
