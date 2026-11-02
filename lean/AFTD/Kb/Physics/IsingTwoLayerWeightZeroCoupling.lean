import AFTD.Prelude
import AFTD.Kb.Physics.IsingTwoLayerWeight
import AFTD.Kb.Physics.IsingTwoLayerEdgeEnergy
import AFTD.Kb.Physics.IsingRingSpin

/-!
# ising_two_layer_weight_zero_coupling

Topic: statistical_mechanics   Node: cfa7ec084a3b

Provenance: helper lemma. Zero-coupling consistency of the two-layer Gibbs weight for OP-812.

At zero coupling the two-layer Gibbs weight is the product of the separate critical-temperature weights of the two layers.
-/

theorem ising_two_layer_weight_zero_coupling (d n : ℕ)
    (G H : SimpleGraph (Fin n)) (σ τ : Fin n → Bool) :
    ising_two_layer_weight d n 0 G H σ τ =
      Real.exp (Real.artanh (1 / ((d : ℝ) - 1)) * ising_two_layer_edge_energy G σ) *
      Real.exp (Real.artanh (1 / ((d : ℝ) - 1)) * ising_two_layer_edge_energy H τ) := by
  simp only [ising_two_layer_weight, zero_mul, add_zero, mul_add, Real.exp_add]
