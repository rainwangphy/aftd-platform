import AFTD.Prelude

/-!
# cayley_table_graph

Topic: combinatorics   Node: b97bb1ee8b86

Provenance: formalization of a published result. Source: arXiv:2611.13274 Sec. 1

The Latin square graph of the Cayley table of a magma G is the simple graph with vertex set G × G where two distinct vertices (g₁, h₁) and (g₂, h₂) are adjacent if they share a row (g₁ = g₂), a column (h₁ = h₂), or a product symbol (g₁ * h₁ = g₂ * h₂).
-/

/-- The Latin square graph of the Cayley table of a magma G, with vertices G × G and edges between distinct cells sharing row, column, or symbol. -/
def cayley_table_graph (G : Type*) [Mul G] : SimpleGraph (G × G) where
  Adj u v := u ≠ v ∧ (u.1 = v.1 ∨ u.2 = v.2 ∨ u.1 * u.2 = v.1 * v.2)
