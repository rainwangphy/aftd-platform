import AFTD.Prelude
import AFTD.Kb.Physics.WaveEquation1D
import AFTD.Kb.Physics.KleinGordonEquation1D

/-!
# klein_gordon_zero_mass_iff_wave_equation

Topic: classical_fields   Node: ace672376fdb

Provenance: formalization of a published result. Source: standard textbook result (classical field theory: the massless Klein-Gordon equation is the wave equation)

A scalar field φ : ℝ × ℝ → ℝ satisfies the one-dimensional Klein-Gordon equation with mass parameter 0 and speed c if and only if it satisfies the one-dimensional wave equation with speed c.
-/

/-- In the massless limit m = 0, the 1D Klein-Gordon equation is equivalent to the 1D wave equation. -/
theorem klein_gordon_zero_mass_iff_wave_equation (c : ℝ) (φ : ℝ × ℝ → ℝ) :
    KleinGordonEquation1D 0 c φ ↔ WaveEquation1D c φ := by
  dsimp [KleinGordonEquation1D, WaveEquation1D]
  simp [sub_eq_zero]
