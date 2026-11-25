import AFTD.Prelude
import AFTD.Kb.Tcs.Multigraph
import AFTD.Kb.Tcs.MultigraphDegree

/-!
# multigraph_max_degree

Topic: graphs   Node: cccfc7dbd23e

Provenance: formalization of a published result. Source: scout/2611-29111-when-do-local-bounds-permit-optimal-edge-colorings.md:87

The maximum degree Delta(G) of a multigraph G on a finite vertex type V is the maximum over all vertices u of the degree of u.
-/

/-- The maximum degree Delta(G) of a multigraph G. -/
def multigraph_max_degree {V : Type*} [Fintype V] (G : Multigraph V) : ℕ := Finset.univ.sup (fun u => multigraph_degree G u)
