import AFTD.Prelude
import AFTD.Kb.Physics.IsLorentzMatrix
import AFTD.Kb.Physics.MinkowskiMatrix

/-!
# is_lorentz_matrix_mul

Topic: special_relativity   Node: 2fbf295df04e

If A and B are 4x4 Lorentz matrices, then their matrix product A * B is also a Lorentz matrix.
-/

/-- The product of two Lorentz matrices is a Lorentz matrix. -/
theorem is_lorentz_matrix_mul {A B : Matrix (Fin 4) (Fin 4) ℝ} (hA : is_lorentz_matrix A) (hB : is_lorentz_matrix B) : is_lorentz_matrix (A * B) := by
  dsimp [is_lorentz_matrix] at *
  rw [Matrix.transpose_mul]
  calc
    (B.transpose * A.transpose) * minkowski_matrix * (A * B)
      = B.transpose * (A.transpose * minkowski_matrix * A) * B := by simp only [Matrix.mul_assoc]
    _ = B.transpose * minkowski_matrix * B := by rw [hA]
    _ = minkowski_matrix := hB
