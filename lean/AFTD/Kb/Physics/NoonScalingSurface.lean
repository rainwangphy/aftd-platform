import AFTD.Prelude
import AFTD.Kb.Physics.BesselI0

/-!
# noon_scaling_surface

Topic: quantum_mechanics   Node: 7c13bf2d5015

Provenance: formalization of a published result. Source: arXiv:2611.17021

For real balance parameter q and real loss parameters a, b, the asymptotic realignment scaling surface is defined as F_q(a, b) = q^2 * Real.exp (-2*a) * bessel_I0 (2*a) + (1-q)^2 * Real.exp (-2*b) * bessel_I0 (2*b) + 2 * q * (1-q) * Real.exp (-(a+b)) * bessel_I0 (2 * Real.sqrt (a*b)) + 4 * q * (1-q) * Real.exp (-(a+b)).
-/

/-- The asymptotic realignment scaling surface F_q(a, b) in the high-photon, low-loss scaling regime. -/
noncomputable def noon_scaling_surface (q a b : ℝ) : ℝ :=
  q ^ 2 * Real.exp (-2 * a) * bessel_I0 (2 * a) +
  (1 - q) ^ 2 * Real.exp (-2 * b) * bessel_I0 (2 * b) +
  2 * q * (1 - q) * Real.exp (-(a + b)) * bessel_I0 (2 * Real.sqrt (a * b)) +
  4 * q * (1 - q) * Real.exp (-(a + b))
