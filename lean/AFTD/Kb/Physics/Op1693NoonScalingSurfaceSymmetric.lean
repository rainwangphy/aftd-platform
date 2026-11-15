import AFTD.Prelude
import AFTD.Kb.Physics.BesselI0
import AFTD.Kb.Physics.NoonScalingSurface

/-!
# op_1693_noon_scaling_surface_symmetric

Topic: quantum_mechanics   Node: 511e474b9b1d

Provenance: formalization of a published result. Source: arXiv:2611.17021

For any non-negative real loss a, at balanced amplitude q = 1/2 the asymptotic scaling surface satisfies noon_scaling_surface (1 / 2) a a = Real.exp (-2 * a) * (bessel_I0 (2 * a) + 1).
-/

/-- Simplification of the asymptotic scaling surface at balanced amplitude q = 1/2 and symmetric loss a = b. -/
theorem op_1693_noon_scaling_surface_symmetric (a : ℝ) (ha : 0 ≤ a) :
    noon_scaling_surface (1 / 2) a a = Real.exp (-2 * a) * (bessel_I0 (2 * a) + 1) := by
  simp only [noon_scaling_surface]
  rw [Real.sqrt_mul_self ha]
  ring_nf
