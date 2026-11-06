import AFTD.Prelude
import AFTD.Kb.Tcs.CubicEdge

/-!
# CubicHypergraph

Topic: quantum   Node: 69d6af48db57

Provenance: formalization of a published result. Source: Quantum 8, 1422 (2024)

For a natural number n, CubicHypergraph n is the type of finite sets of 3-element subsets of Fin n, representing the edge set of a 3-uniform hypergraph on n vertices.
-/

/-- The type of 3-uniform hypergraphs on Fin n. -/
abbrev CubicHypergraph (n : ℕ) := Finset (CubicEdge n)
