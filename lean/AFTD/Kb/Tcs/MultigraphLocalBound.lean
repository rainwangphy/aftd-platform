import AFTD.Prelude
import AFTD.Kb.Tcs.Multigraph
import AFTD.Kb.Tcs.MultigraphDegree
import AFTD.Kb.Tcs.MultigraphMaxMultAt

/-!
# multigraph_local_bound

Topic: graphs   Node: 6a10ec39a8a8

Provenance: formalization of a published result. Source: scout/2611-29111-when-do-local-bounds-permit-optimal-edge-colorings.md:95

The local Vizing bound b_G(u, v) for vertices u and v in a multigraph G on a finite vertex type V, defined as max(d_G(u) + mu_G(u), d_G(v) + mu_G(v)).
-/

/-- The local Vizing bound b_G(u, v) = max(d(u) + mu(u), d(v) + mu(v)). -/
def multigraph_local_bound {V : Type*} [Fintype V] (G : Multigraph V) (u v : V) : ℕ := max (multigraph_degree G u + multigraph_max_mult_at G u) (multigraph_degree G v + multigraph_max_mult_at G v)
