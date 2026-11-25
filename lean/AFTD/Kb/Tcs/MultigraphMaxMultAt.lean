import AFTD.Prelude
import AFTD.Kb.Tcs.Multigraph

/-!
# multigraph_max_mult_at

Topic: graphs   Node: 260779ec2d32

Provenance: formalization of a published result. Source: scout/2611-29111-when-do-local-bounds-permit-optimal-edge-colorings.md:87

The maximum edge multiplicity mu_G(u) at vertex u in a multigraph G on a finite vertex type V.
-/

/-- The maximum edge multiplicity incident to vertex u in G. -/
def multigraph_max_mult_at {V : Type*} [Fintype V] (G : Multigraph V) (u : V) : ℕ := Finset.univ.sup (fun v => G.mult u v)
