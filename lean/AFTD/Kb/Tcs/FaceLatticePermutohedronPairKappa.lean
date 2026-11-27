import AFTD.Prelude
import AFTD.Kb.Tcs.FaceLatticePermutohedronBlockWeight

/-!
# face_lattice_permutohedron_pair_kappa

Topic: combinatorics   Node: eea6f73d550d

Provenance: formalization of a published result. Source: arXiv:2611.34537 Section 3

The pair edge weight kappa(x, y) is defined as w(x + y) divided by the binomial coefficient choose(x + y, x).
-/

/-- Pair edge weight kappa(x, y) = w(x + y) / choose(x + y, x). -/
def face_lattice_permutohedron_pair_kappa (x y : ℕ) : ℚ :=
  (face_lattice_permutohedron_block_weight (x + y) : ℚ) / ((Nat.choose (x + y) x : ℚ))
