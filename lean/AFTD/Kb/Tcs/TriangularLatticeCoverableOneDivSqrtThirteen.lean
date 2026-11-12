import AFTD.Prelude
import AFTD.Kb.Tcs.TriangularLattice
import AFTD.Kb.Tcs.IsCoverable
import AFTD.Kb.Tcs.TriangularLatticeCoverableCriticalSpacings

/-!
# triangular_lattice_coverable_one_div_sqrt_thirteen

Topic: combinatorics   Node: 5e3ef62f15d9

Provenance: helper lemma. arXiv:2611.13535 Theorem C -- Covering the Triangular Lattice with Non-Overlapping Unit Disks

The triangular lattice with spacing d = 1 / Real.sqrt 13 is coverable by non-overlapping closed unit disks.
-/

/-- The triangular lattice with spacing 1 / √13 is coverable by non-overlapping unit disks. -/
theorem triangular_lattice_coverable_one_div_sqrt_thirteen : is_coverable (triangular_lattice (1 / Real.sqrt 13)) := triangular_lattice_coverable_critical_spacings.1
