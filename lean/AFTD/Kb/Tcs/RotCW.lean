import AFTD.Prelude

/-!
# rotCW

Topic: combinatorics   Node: 1f99b572594c

Provenance: formalization of a published result. Source: arXiv:2611.12329 Piercing a Chessboard with Restricted Slopes, Section 1

The clockwise quarter-turn rotation on pairs of natural numbers (ℕ × ℕ) parameterized by n : ℕ maps (x, y) to (y, n - 1 - x).
-/

/-- Clockwise quarter-turn rotation of a pair of natural numbers on the n x n chessboard. -/
def rotCW (n : ℕ) : (ℕ × ℕ) → (ℕ × ℕ) := fun ⟨x, y⟩ => (y, n - 1 - x)
