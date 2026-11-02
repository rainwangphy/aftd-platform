import AFTD.Prelude
import AFTD.Kb.Physics.IsingTwoLayerQuarticDensity

/-!
# ising_two_layer_quartic_expectation

Topic: statistical_mechanics   Node: 68d093a6469c

Provenance: helper lemma. Auxiliary definition for OP-812, critical two-layer random regular Ising crossover.

The target expectation is the Lebesgue integral of a bounded continuous test function times the quartic density divided by the integral of that density on the real plane.
-/

open scoped BigOperators
open MeasureTheory

noncomputable def ising_two_layer_quartic_expectation (d : ℕ) (c : ℝ)
    (f : BoundedContinuousFunction (ℝ × ℝ) ℝ) : ℝ :=
  (∫ p : ℝ × ℝ, f p * ising_two_layer_quartic_density d c p) /
  (∫ p : ℝ × ℝ, ising_two_layer_quartic_density d c p)
