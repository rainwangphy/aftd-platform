import AFTD.Prelude
import AFTD.Kb.Physics.IsLorentzMatrix

/-!
# is_lorentz_matrix_one

Topic: special_relativity   Node: 34013e198ff9

The 4x4 identity matrix is a Lorentz matrix.
-/

/-- The 4x4 identity matrix is a Lorentz matrix. -/
theorem is_lorentz_matrix_one : is_lorentz_matrix 1 := by
  simp [is_lorentz_matrix]
