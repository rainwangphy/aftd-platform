import AFTD.Prelude
import AFTD.Kb.Physics.IsingRingSpin
import AFTD.Kb.Physics.IsingTwoLayerEdgeEnergy

/-!
# ising_two_layer_weight

Topic: statistical_mechanics   Node: 1c9fb434f546

Provenance: helper lemma. Auxiliary definition for OP-812, critical two-layer random regular Ising crossover.

The two-layer Gibbs weight is the exponential of the critical intralayer energy plus c times n to the power negative one half times the overlap of the two spin configurations.
-/

open scoped BigOperators
open MeasureTheory

noncomputable def ising_two_layer_weight (d n : ℕ) (c : ℝ)
    (G H : SimpleGraph (Fin n)) (σ τ : Fin n → Bool) : ℝ :=
  Real.exp (Real.artanh (1 / ((d : ℝ) - 1)) *
    (ising_two_layer_edge_energy G σ + ising_two_layer_edge_energy H τ) +
    c * (n : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ v, ising_ring_spin (σ v) * ising_ring_spin (τ v))
