import AFTD.Prelude

/-!
# minkowski_matrix

Topic: special_relativity   Node: b99ec63919f9

The Minkowski metric matrix on ℝ⁴ with mostly-plus signature (-, +, +, +) is the 4x4 diagonal matrix with diagonal entries -1, 1, 1, 1.
-/

/-- The standard Minkowski metric matrix with signature (-, +, +, +) on ℝ⁴. -/
def minkowski_matrix : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![-1, 1, 1, 1]
