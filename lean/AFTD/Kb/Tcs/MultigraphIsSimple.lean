import AFTD.Prelude
import AFTD.Kb.Tcs.Multigraph

/-!
# multigraph_is_simple

Topic: graphs   Node: b0ef8b2d6eaf

Provenance: formalization of a published result. Source: scout/2611-29111-when-do-local-bounds-permit-optimal-edge-colorings.md:87

A multigraph G is simple if every edge multiplicity is at most one.
-/

/-- Predicate that a multigraph is simple (all multiplicities at most 1). -/
def multigraph_is_simple {V : Type*} (G : Multigraph V) : Prop := ∀ u v, G.mult u v ≤ 1
