import AFTD.Prelude
import AFTD.Kb.Physics.WaveEquation1D

/-!
# wave_equation_zero

Topic: classical_fields   Node: 7b76f64a2998

Provenance: original. Related work: machine-posed sanity statement for the one-dimensional wave equation; no novelty claimed

The zero function is a solution to the one-dimensional wave equation.
-/

/-- The zero function is a solution to the one-dimensional wave equation. -/
theorem wave_equation_zero (c : ℝ) : WaveEquation1D c (fun _ => 0) := by
  simp [WaveEquation1D]
