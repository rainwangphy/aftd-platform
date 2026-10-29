import AFTD.Prelude
import AFTD.Kb.Tcs.IsEdgeGeodesicTransversal

/-!
# edge_geodesic_transversal_number

Topic: graphs   Node: 4d022ec96df7

Provenance: formalization of a published result. Source: arXiv:2610.36821 Section 1

The edge geodesic transversal number of a simple graph G is the infimum in ℕ of the set of natural numbers k such that there exists a finite edge geodesic transversal S of G (satisfying is_edge_geodesic_transversal G S) with cardinality k.
-/

/-- The edge geodesic transversal number gt_e(G) of a simple graph G. -/
noncomputable def edge_geodesic_transversal_number {V : Type*} (G : SimpleGraph V) : ℕ := sInf { k : ℕ | ∃ S : Finset (Sym2 V), is_edge_geodesic_transversal G S ∧ S.card = k }
