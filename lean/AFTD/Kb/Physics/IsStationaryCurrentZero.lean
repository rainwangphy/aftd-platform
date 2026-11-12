import AFTD.Prelude
import AFTD.Kb.Physics.SimpleGraphOrientation
import AFTD.Kb.Physics.IsStationaryCurrent
import AFTD.Kb.Physics.DephasedTreeLocalNoiseCriterionZero

/-!
# is_stationary_current_zero

Topic: statistical_mechanics   Node: fb0d763dd2d7

Provenance: helper lemma. folklore

For any finite simple graph G and any orientation o of G, the zero current assigning 0 to each edge is stationary.
-/

/-- The zero current is a stationary current on any oriented simple graph. -/
theorem is_stationary_current_zero {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (o : SimpleGraphOrientation G) :
    is_stationary_current G o (fun _ => 0) := by first | exact dephased_tree_local_noise_criterion_zero | (apply dephased_tree_local_noise_criterion_zero <;> assumption) | (apply dephased_tree_local_noise_criterion_zero <;> simp_all) | simpa using dephased_tree_local_noise_criterion_zero | (simp only [SimpleGraphOrientation, is_stationary_current] at *; first | exact dephased_tree_local_noise_criterion_zero | (apply dephased_tree_local_noise_criterion_zero <;> assumption) | (apply dephased_tree_local_noise_criterion_zero <;> simp_all) | simpa using dephased_tree_local_noise_criterion_zero)
