import AFTD.Prelude
import AFTD.Kb.Tcs.Chessboard

/-!
# asTrace

Topic: combinatorics   Node: 5e0db343d35a

Provenance: formalization of a published result. Source: arXiv:2611.12329 Piercing a Chessboard with Restricted Slopes, Section 1

The trace of an ascending shallow path with coordinate function a : ℤ → ℤ on the n × n chessboard is the finite set of cells in chessboard n satisfying a(x + y) = x.
-/

/-- The trace of an AS path on the n x n chessboard. -/
def asTrace (n : ℕ) (a : ℤ → ℤ) : Finset (ℕ × ℕ) := (chessboard n).filter (fun p => a (p.1 + p.2) = p.1)
