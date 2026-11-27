import AFTD.Prelude
import AFTD.Kb.Tcs.FaceLatticePermutohedronBlockWeight

/-!
# face_lattice_permutohedron_block_omega

Topic: combinatorics   Node: f7d6b0dd5055

Provenance: formalization of a published result. Source: arXiv:2611.34537 Section 3

The potential Omega(s) is 0 for s ≤ 1 and (s - 1) * w(s) for s ≥ 2.
-/

/-- Potential function Omega on block sizes for the fractional flow below the mode. -/
def face_lattice_permutohedron_block_omega (s : ℕ) : ℕ :=
  if s ≤ 1 then 0
  else (s - 1) * face_lattice_permutohedron_block_weight s
