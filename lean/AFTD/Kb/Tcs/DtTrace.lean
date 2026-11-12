import AFTD.Prelude
import AFTD.Kb.Tcs.AsTrace
import AFTD.Kb.Tcs.RotCW

/-!
# dtTrace

Topic: combinatorics   Node: 16cd7d511edf

Provenance: formalization of a published result. Source: arXiv:2611.12329 Piercing a Chessboard with Restricted Slopes, Section 1

The trace of a descending steep (DT) path with underlying AS coordinate function a : ℤ → ℤ on the n × n chessboard is the image of asTrace n a under the rotation rotCW n.
-/

/-- The trace of a descending steep (DT) path on the n x n chessboard. -/
def dtTrace (n : ℕ) (a : ℤ → ℤ) : Finset (ℕ × ℕ) := (asTrace n a).image (rotCW n)
