import AFTD.Prelude
import AFTD.Kb.Tcs.Multigraph

/-!
# multigraph_is_proper_edge_coloring

Topic: graphs   Node: ad1a036a42a1

Provenance: formalization of a published result. Source: scout/2611-29111-when-do-local-bounds-permit-optimal-edge-colorings.md:83

A proper k-edge-coloring of a multigraph G assigns each pair of vertices u and v a finset of colors in {1, ..., k} of cardinality mult u v such that color sets of adjacent pairs sharing a vertex are disjoint.
-/

/-- Predicate that c is a proper k-edge-coloring of G using colors in {1, ..., k}. -/
def multigraph_is_proper_edge_coloring {V : Type*} (G : Multigraph V) (k : ℕ) (c : V → V → Finset ℕ) : Prop := (∀ u v, c u v = c v u) ∧ (∀ u v, (c u v).card = G.mult u v) ∧ (∀ u v, ∀ x ∈ c u v, 1 ≤ x ∧ x ≤ k) ∧ (∀ u, ∀ v₁ v₂, v₁ ≠ v₂ → Disjoint (c u v₁) (c u v₂))
