import AFTD.Prelude
import AFTD.Kb.Physics.IsingRingSpin

/-!
# ising_two_layer_edge_energy

Topic: statistical_mechanics   Node: 575f3d10e097

Provenance: helper lemma. Auxiliary definition for OP-812, critical two-layer random regular Ising crossover.

The edge energy is the sum, over the unordered edges of the graph, of the products of the endpoint spins.
-/

open scoped BigOperators
open MeasureTheory

noncomputable def ising_two_layer_edge_energy {n : ℕ} (G : SimpleGraph (Fin n))
    (σ : Fin n → Bool) : ℝ := by
  classical
  exact ∑ e ∈ G.edgeFinset,
    Sym2.lift ⟨fun u v => ising_ring_spin (σ u) * ising_ring_spin (σ v),
      fun u v => mul_comm _ _⟩ e
