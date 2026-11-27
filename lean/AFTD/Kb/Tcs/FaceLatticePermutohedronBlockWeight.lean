import AFTD.Prelude

/-!
# face_lattice_permutohedron_block_weight

Topic: combinatorics   Node: b7158bd0b519

Provenance: formalization of a published result. Source: arXiv:2611.34537 Section 3

The weight w(s) is 11 for s = 2, 12 for s = 3, and 14 for all s ≥ 4 (and s ≤ 1).
-/

/-- Weight function w on block sizes for the fractional flow below the mode. -/
def face_lattice_permutohedron_block_weight (s : ℕ) : ℕ :=
  if s = 2 then 11
  else if s = 3 then 12
  else 14
