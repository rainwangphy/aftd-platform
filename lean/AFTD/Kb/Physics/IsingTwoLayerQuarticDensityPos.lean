import AFTD.Prelude
import AFTD.Kb.Physics.IsingTwoLayerQuarticDensity

/-!
# ising_two_layer_quartic_density_pos

Topic: statistical_mechanics   Node: 4cded9037ff7

Provenance: helper lemma. Positivity sanity check for the target density in OP-812.

The unnormalized two-layer quartic density is strictly positive everywhere.
-/

theorem ising_two_layer_quartic_density_pos (d : ℕ) (c : ℝ) (p : ℝ × ℝ) : 0 < ising_two_layer_quartic_density d c p := by
  unfold ising_two_layer_quartic_density
  exact Real.exp_pos _
