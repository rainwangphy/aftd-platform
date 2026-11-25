import AFTD.Prelude
import AFTD.Kb.Tcs.Multigraph

/-!
# multigraph_degree

Topic: graphs   Node: 3a577e3fa3c6

Provenance: formalization of a published result. Source: scout/2611-29111-when-do-local-bounds-permit-optimal-edge-colorings.md:87

The degree of a vertex u in a multigraph G on a finite vertex type V is the sum of edge multiplicities of edges incident to u.
-/

/-- The degree of a vertex u in a multigraph G. -/
def multigraph_degree {V : Type*} [Fintype V] (G : Multigraph V) (u : V) : ℕ := ∑ v, G.mult u v
