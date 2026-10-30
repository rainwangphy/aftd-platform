import AFTD.Prelude
import AFTD.Kb.Tcs.IsGeodesicTransversal

/-!
# geodesic_transversal_number

Topic: graphs   Node: f9a9a52fbde1

Provenance: formalization of a published result. Source: scout/2610-36821-the-edge-geodesic-transversal-problem.md:85

The geodesic transversal number gt(G) of a simple graph G is the infimum in ℕ of the set of natural numbers k such that there exists a finite geodesic transversal S of G with cardinality k.
-/

/-- The geodesic transversal number of a simple graph G is the infimum in ℕ of the cardinalities of all finite geodesic transversals of G. -/
noncomputable def geodesic_transversal_number {V : Type*} (G : SimpleGraph V) : ℕ := sInf { k : ℕ | ∃ S : Finset V, is_geodesic_transversal G S ∧ S.card = k }
