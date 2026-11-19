import AFTD.Prelude
import AFTD.Kb.Physics.Op2046Matrix

/-!
# op2046_spectrum

Topic: quantum_mechanics   Node: 7110c108b634

Provenance: helper lemma. OP-2046; Gaussian Wishart definition in arXiv:2406.03335, Section 1.

Eigenvalue list of the Hermitian Gram matrix of the complex matrix; the order is not assumed.
-/

open scoped BigOperators Matrix Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section

noncomputable def op2046_spectrum (n m : ℕ) (x : (Fin n × Fin m × Fin 2) → ℝ) : Fin n → ℝ :=
  (Matrix.isHermitian_mul_conjTranspose_self (op2046_matrix n m x)).eigenvalues
