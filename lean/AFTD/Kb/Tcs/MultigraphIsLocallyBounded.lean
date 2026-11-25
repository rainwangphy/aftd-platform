import AFTD.Prelude
import AFTD.Kb.Tcs.Multigraph
import AFTD.Kb.Tcs.MultigraphLocalBound

/-!
# multigraph_is_locally_bounded

Topic: graphs   Node: b20f3d63c5a8

Provenance: formalization of a published result. Source: scout/2611-29111-when-do-local-bounds-permit-optimal-edge-colorings.md:95

An edge-coloring c of a multigraph G is locally bounded if for all vertices u and v, each color in c u v is at most the local bound b_G(u, v).
-/

/-- Predicate that each edge between u and v receives a color at most b_G(u, v). -/
def multigraph_is_locally_bounded {V : Type*} [Fintype V] (G : Multigraph V) (c : V → V → Finset ℕ) : Prop := ∀ u v, ∀ x ∈ c u v, x ≤ multigraph_local_bound G u v
