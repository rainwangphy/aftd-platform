import AFTD.Prelude
import AFTD.Kb.Physics.IsingTwoLayerWeight
import AFTD.Kb.Physics.IsingTwoLayerObservable

/-!
# ising_two_layer_gibbs_expectation

Topic: statistical_mechanics   Node: 8e82ccd4e741

Provenance: helper lemma. Auxiliary definition for OP-812, critical two-layer random regular Ising crossover.

The finite Gibbs expectation of a bounded continuous test function is the sum over both spin configurations of its value at the scaled magnetization pair times the Gibbs weight, divided by the sum of the weights.
-/

open scoped BigOperators
open MeasureTheory

noncomputable def ising_two_layer_gibbs_expectation (d n : ℕ) (c : ℝ)
    (G H : SimpleGraph (Fin n)) (f : BoundedContinuousFunction (ℝ × ℝ) ℝ) : ℝ :=
  (∑ σ : Fin n → Bool, ∑ τ : Fin n → Bool,
    ising_two_layer_weight d n c G H σ τ * f (ising_two_layer_observable n σ τ)) /
  (∑ σ : Fin n → Bool, ∑ τ : Fin n → Bool, ising_two_layer_weight d n c G H σ τ)
