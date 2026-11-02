import AFTD.Prelude
import AFTD.Kb.Physics.IsingRingSpin

/-!
# ising_two_layer_observable

Topic: statistical_mechanics   Node: 72713910eae6

Provenance: helper lemma. Auxiliary definition for OP-812, critical two-layer random regular Ising crossover.

The observable is the pair of total layer magnetizations, each multiplied by n to the power negative three quarters.
-/

open scoped BigOperators
open MeasureTheory

noncomputable def ising_two_layer_observable (n : ℕ) (σ τ : Fin n → Bool) : ℝ × ℝ :=
  ((n : ℝ) ^ (-(3 / 4 : ℝ)) * ∑ v, ising_ring_spin (σ v),
   (n : ℝ) ^ (-(3 / 4 : ℝ)) * ∑ v, ising_ring_spin (τ v))
