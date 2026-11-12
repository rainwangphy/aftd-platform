import AFTD.Prelude
import AFTD.Kb.Tcs.TriangularLattice
import AFTD.Kb.Tcs.IsCoverable
import AFTD.Kb.Tcs.TriangularLatticeCoverableCriticalSpacings

/-!
# triangular_lattice_coverable_two_div_sqrt_twenty_one

Topic: combinatorics   Node: c92d1d3386d7

Provenance: helper lemma. arXiv:2611.13535 Theorem C -- Covering the Triangular Lattice with Non-Overlapping Unit Disks

The triangular lattice with spacing d = 2 / Real.sqrt 21 is coverable by non-overlapping closed unit disks.
-/

/-- The triangular lattice with spacing 2 / √21 is coverable by non-overlapping unit disks. -/
theorem triangular_lattice_coverable_two_div_sqrt_twenty_one : is_coverable (triangular_lattice (2 / Real.sqrt 21)) := triangular_lattice_coverable_critical_spacings.2
