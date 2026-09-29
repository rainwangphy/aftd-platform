import AFTD.Prelude

/-!
# WaveEquation1D

Topic: classical_fields   Node: 96a4e9ddb89b

A scalar field u : ℝ × ℝ → ℝ satisfies the one-dimensional wave equation with wave speed c if for all (x, t), the second partial derivative of u with respect to time equals c^2 times the second partial derivative of u with respect to space.
-/

/-- A scalar field u satisfies the 1D wave equation with speed c if d^2/dt^2 u = c^2 d^2/dx^2 u. -/
def WaveEquation1D (c : ℝ) (u : ℝ × ℝ → ℝ) : Prop :=
  ∀ x t : ℝ, deriv (deriv (fun s => u (x, s))) t = c^2 * deriv (deriv (fun y => u (y, t))) x
