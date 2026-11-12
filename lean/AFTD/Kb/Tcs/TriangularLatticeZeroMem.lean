import AFTD.Prelude
import AFTD.Kb.NumberTheory.EisensteinOmega
import AFTD.Kb.Tcs.TriangularLattice

/-!
# triangular_lattice_zero_mem

Topic: combinatorics   Node: fca03a2608a7

Provenance: helper lemma. arXiv:2611.13535, Section 2

For every real number d, the origin 0 belongs to the triangular lattice with spacing d.
-/

/-- The origin is an element of the triangular lattice for any spacing parameter d. -/
theorem triangular_lattice_zero_mem (d : ℝ) : (0 : ℂ) ∈ triangular_lattice d := by
  exact ⟨0, 0, by simp⟩
