import AFTD.Prelude
import AFTD.Kb.Tcs.CycleRookPoly

/-!
# cycle_rook_poly_one

Topic: combinatorics   Node: 069d0dc3ca59

Provenance: helper lemma. arXiv:2610.23958 Proposition 5.1

The rook polynomial of a 1-cycle is equal to 1 in ℚ[x].
-/

/-- Sanity check: Q_1(X) = 1. -/
theorem cycle_rook_poly_one : cycle_rook_poly 1 = 1 := by
  simp [cycle_rook_poly]
