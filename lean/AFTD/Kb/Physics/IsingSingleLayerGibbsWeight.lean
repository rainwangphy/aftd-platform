import AFTD.Prelude
import AFTD.Kb.Physics.IsingTwoLayerEdgeEnergy

/-!
# ising_single_layer_gibbs_weight

Topic: statistical_mechanics   Node: 0c7ea7e1ed5b

Provenance: helper lemma. step towards critical_regular_ising_two_layer_weak_matching_quartic_crossover

The critical single-layer Gibbs weight of a spin configuration σ on a graph G on Fin n: exp(β_c · E_G(σ)) where E_G is the edge energy and β_c = artanh(1/(d-1)) is the critical inverse temperature.
-/

/-- Critical single-layer Gibbs weight exp(β_c · E_G(σ)), β_c = artanh(1/(d-1)). -/
noncomputable def ising_single_layer_gibbs_weight (d n : ℕ) (G : SimpleGraph (Fin n)) (σ : Fin n → Bool) : ℝ := Real.exp (Real.artanh (1 / ((d : ℝ) - 1)) * ising_two_layer_edge_energy G σ)
