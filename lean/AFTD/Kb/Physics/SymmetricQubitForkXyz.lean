import AFTD.Prelude
import AFTD.Kb.Physics.QubitState0
import AFTD.Kb.Physics.QubitState1

/-!
# symmetric_qubit_fork_xyz

Topic: quantum_mechanics   Node: f50ad6d5e342

Provenance: formalization of a published result. Source: OP-1440

The tripartite real matrix symmetric_qubit_fork_xyz p a q t of type Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℝ for real parameters p, a, q, t : ℝ, defined by p • (Matrix.diagonal ![1, 0]).kronecker ((qubit_state_0 a t).kronecker (qubit_state_0 a t)) + (1 - p) • (Matrix.diagonal ![0, 1]).kronecker ((qubit_state_1 q).kronecker (qubit_state_1 q)).
-/

/-- The tripartite state rho_XYZ on Fin 2 x (Fin 2 x Fin 2). -/
noncomputable def symmetric_qubit_fork_xyz (p a q t : ℝ) :
    Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℝ := let s0 := qubit_state_0 a t
  let s1 := qubit_state_1 q
  let p0 : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, 0]
  let p1 : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![0, 1]
  p • (p0.kronecker (s0.kronecker s0)) + (1 - p) • (p1.kronecker (s1.kronecker s1))
