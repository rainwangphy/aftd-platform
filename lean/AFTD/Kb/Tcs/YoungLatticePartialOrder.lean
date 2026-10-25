import AFTD.Prelude
import AFTD.Kb.Tcs.YoungLattice

/-!
# young_lattice_partial_order

Topic: combinatorics   Node: 9c453cbe9007

Provenance: formalization of a published result. Source: arXiv:2610.24148, Section 2.7.4

The Young lattice L(m, n) inherits the partial order on Young diagrams given by cell inclusion.
-/

/-- Partial order on YoungLattice m n induced by the inclusion order on YoungDiagram. -/
instance young_lattice_partial_order (m n : ℕ) : PartialOrder (YoungLattice m n) := inferInstanceAs (PartialOrder { μ : YoungDiagram // ∀ c ∈ μ, c.1 < m ∧ c.2 < n })
