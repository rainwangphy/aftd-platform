import AFTD.Prelude

/-!
# matrixFrobeniusNormSq

Topic: quantum_mechanics   Node: 1034a38ffb70

Provenance: formalization of a published result. Source: Horn and Johnson, Matrix Analysis, Section 5.6

The squared Frobenius norm of a d by d complex matrix M is the sum over all matrix entries of the squared absolute value |M_{ij}|^2.
-/

/-- Squared Frobenius norm of a d by d complex matrix M. -/
def matrixFrobeniusNormSq {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (M i j)
