import AFTD.Prelude

/-!
# qubit_state_1

Topic: quantum_mechanics   Node: df9c6be16cbd

Provenance: formalization of a published result. Source: OP-1440

The diagonal qubit state sigma_1 with eigenvalues 1-q and q.
-/

/-- The diagonal qubit density matrix sigma_1 = diag(1-q, q). -/
def qubit_state_1 (q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1 - q, q]
