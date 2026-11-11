import AFTD.Prelude

/-!
# qubit_rotation

Topic: quantum_mechanics   Node: 05cbb8c95733

Provenance: formalization of a published result. Source: OP-1440

The 2x2 real matrix qubit_rotation t of type Matrix (Fin 2) (Fin 2) ℝ for a real parameter t : ℝ, with row 0 equal to ![(1 - t^2) / (1 + t^2), -2 * t / (1 + t^2)] and row 1 equal to ![2 * t / (1 + t^2), (1 - t^2) / (1 + t^2)].
-/

/-- The 2x2 Cayley rotation matrix with parameter t. -/
noncomputable def qubit_rotation (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := ![![ (1 - t^2) / (1 + t^2), -2 * t / (1 + t^2) ],
      ![ 2 * t / (1 + t^2), (1 - t^2) / (1 + t^2) ]]
