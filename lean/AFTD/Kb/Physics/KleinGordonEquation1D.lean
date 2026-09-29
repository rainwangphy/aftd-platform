import AFTD.Prelude

/-!
# KleinGordonEquation1D

Topic: classical_fields   Node: eb864ef3654e

A scalar field φ : ℝ × ℝ → ℝ satisfies the one-dimensional Klein-Gordon equation with mass parameter m and propagation speed c if for all (x, t), the second time derivative minus c^2 times the second spatial derivative plus m^2 * φ(x, t) equals zero.
-/

/-- A real scalar field satisfies the 1D Klein-Gordon equation with mass m and speed c if d^2/dt^2 φ - c^2 d^2/dx^2 φ + m^2 φ = 0. -/
def KleinGordonEquation1D (m c : ℝ) (φ : ℝ × ℝ → ℝ) : Prop :=
  ∀ x t : ℝ, deriv (deriv (fun s => φ (x, s))) t - c^2 * deriv (deriv (fun y => φ (y, t))) x + m^2 * φ (x, t) = 0
