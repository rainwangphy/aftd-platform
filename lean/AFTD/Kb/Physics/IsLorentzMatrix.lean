import AFTD.Prelude
import AFTD.Kb.Physics.MinkowskiMatrix

/-!
# is_lorentz_matrix

Topic: special_relativity   Node: 2b9172287688

A 4x4 real matrix Λ is a Lorentz matrix if it preserves the Minkowski metric matrix, satisfying Λᵀ * minkowski_matrix * Λ = minkowski_matrix.
-/

/-- Predicate stating that a 4x4 real matrix is a Lorentz transformation matrix. -/
def is_lorentz_matrix (Λ : Matrix (Fin 4) (Fin 4) ℝ) : Prop := Λ.transpose * minkowski_matrix * Λ = minkowski_matrix
