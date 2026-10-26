import AFTD.Prelude

/-!
# is_locally_dense

Topic: graphs   Node: 8f9ee32a2a81

Provenance: formalization of a published result. Source: arXiv:2610.13820, Section 1

A graph G is (ρ, d)-dense if every vertex subset U of size at least ρ * |V(G)| spans at least (d / 2) * |U|^2 edges.
-/

/-- A graph G is (ρ, d)-dense if every vertex subset U of size at least ρ * |V(G)| spans at least (d / 2) * |U|^2 edges. -/
def is_locally_dense {β : Type*} [Fintype β]
    (G : SimpleGraph β) (ρ d : ℝ) : Prop := ∀ (U : Finset β), ρ * (Fintype.card β : ℝ) ≤ (U.card : ℝ) →
    (d / 2) * (U.card : ℝ) ^ 2 ≤ (Nat.card (G.induce (U : Set β)).edgeSet : ℝ)
