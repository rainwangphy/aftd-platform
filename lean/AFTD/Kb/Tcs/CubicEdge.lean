import AFTD.Prelude

/-!
# CubicEdge

Topic: quantum   Node: 48781e90cc8b

Provenance: formalization of a published result. Source: Quantum 8, 1422 (2024)

For a natural number n, CubicEdge n is the subtype of 3-element subsets of Fin n, representing a hyperedge in a 3-uniform hypergraph on n vertices.
-/

/-- The subtype of 3-element subsets of Fin n. -/
abbrev CubicEdge (n : ℕ) := { e : Finset (Fin n) // e.card = 3 }
