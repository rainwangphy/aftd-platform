import AFTD.Prelude

/-!
# op2046_matrix

Topic: quantum_mechanics   Node: 944289fca923

Provenance: helper lemma. OP-2046; Gaussian Wishart definition in arXiv:2406.03335, Section 1.

Complex matrix whose real and imaginary coordinates are the supplied real variables.
-/

open scoped BigOperators Matrix Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section

noncomputable def op2046_matrix (n m : ℕ) (x : (Fin n × Fin m × Fin 2) → ℝ) : Matrix (Fin n) (Fin m) ℂ :=
  fun i j => Complex.mk (x (i,j,0)) (x (i,j,1))
