import AFTD.Prelude
import AFTD.Kb.Physics.QubitRotation

/-!
# qubit_state_0

Topic: quantum_mechanics   Node: b403ccdfadeb

Provenance: formalization of a published result. Source: OP-1440

The 2x2 real matrix qubit_state_0 a t of type Matrix (Fin 2) (Fin 2) ℝ for real parameters a, t : ℝ, defined as qubit_rotation t * Matrix.diagonal ![1 - a, a] * (qubit_rotation t).transpose.
-/

/-- The rotated qubit state sigma_0 with eigenvalues 1-a and a. -/
noncomputable def qubit_state_0 (a t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := qubit_rotation t * Matrix.diagonal ![1 - a, a] * (qubit_rotation t).transpose
