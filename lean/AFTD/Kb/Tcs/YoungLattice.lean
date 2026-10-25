import AFTD.Prelude

/-!
# YoungLattice

Topic: combinatorics   Node: 6481d32465ff

Provenance: formalization of a published result. Source: arXiv:2610.24148, Section 2.7.4

The Young lattice L(m, n) is the type of Young diagrams whose cells (i, j) satisfy i < m and j < n, ordered by inclusion.
-/

/-- The Young lattice L(m, n) of integer partitions whose Young diagrams fit inside an m × n bounding box. -/
def YoungLattice (m n : ℕ) : Type := { μ : YoungDiagram // ∀ c ∈ μ, c.1 < m ∧ c.2 < n }
