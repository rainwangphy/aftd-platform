import AFTD.Prelude

/-!
# IsAmplyRegular

Topic: graphs   Node: ae1b77212d6f

Provenance: formalization of a published result. Source: arXiv:2610.36620, Section 1.1

A graph G on a finite vertex set is amply regular with parameters (k, ℓ, μ) if it is regular of degree k, every pair of adjacent vertices has ℓ common neighbors, and every pair of vertices at distance 2 in G has μ common neighbors.
-/

/-- A simple graph G is amply regular with parameters (k, ℓ, μ) if it is regular of degree k, any two adjacent vertices share ℓ common neighbors, and any two vertices at distance 2 share μ common neighbors. -/
structure IsAmplyRegular {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k ℓ μ : ℕ) : Prop where
  regular : G.IsRegularOfDegree k
  adj_commonNeighbors : ∀ ⦃u v : V⦄, G.Adj u v → Fintype.card (G.commonNeighbors u v) = ℓ
  dist_two_commonNeighbors : ∀ ⦃u v : V⦄, G.dist u v = 2 → Fintype.card (G.commonNeighbors u v) = μ
