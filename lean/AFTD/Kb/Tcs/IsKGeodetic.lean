import AFTD.Prelude
import AFTD.Kb.Tcs.IsGeodesic

/-!
# is_k_geodetic

Topic: graphs   Node: 38d3ca839609

Provenance: formalization of a published result. Source: arXiv:2611.05762, Definition 1.1

A simple graph G is K-geodetic if for every pair of distinct vertices u and v, the number of geodesics connecting u and v is at most K.
-/

/-- A simple graph G is K-geodetic if every distinct pair of vertices is connected by at most K geodesics. -/
def is_k_geodetic {V : Type*} (G : SimpleGraph V) (K : ℕ) : Prop := ∀ ⦃u v : V⦄, u ≠ v → Nat.card {p : G.Walk u v // is_geodesic p} ≤ K
