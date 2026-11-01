import AFTD.Prelude

/-!
# real_erf

Topic: information   Node: c6e667679229

Provenance: formalization of a published result. Source: folklore

The Gauss error function erf(z) is defined as (2 / sqrt(pi)) times the integral from 0 to z of exp(-t^2).
-/

/-- The Gauss error function erf(z) = (2 / sqrt pi) int_0^z exp(-t^2) dt. -/
noncomputable def real_erf (z : ℝ) : ℝ := (2 / Real.sqrt Real.pi) * ∫ t in (0 : ℝ)..z, Real.exp (-t ^ 2)
