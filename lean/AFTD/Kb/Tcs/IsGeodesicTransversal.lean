import AFTD.Prelude
import AFTD.Kb.Tcs.IsMaximalGeodesic

/-!
# is_geodesic_transversal

Topic: graphs   Node: 3bd7a350fda4

Provenance: formalization of a published result. Source: scout/2610-36821-the-edge-geodesic-transversal-problem.md:85

A finite set S of vertices in a simple graph G is a geodesic transversal if every maximal geodesic in G contains at least one vertex of S.
-/

/-- A finite set S of vertices of G is a geodesic transversal if every maximal geodesic in G contains at least one vertex of S. -/
def is_geodesic_transversal {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop := ∀ ⦃u v : V⦄ (p : G.Walk u v), is_maximal_geodesic p → ∃ x ∈ S, x ∈ p.support
