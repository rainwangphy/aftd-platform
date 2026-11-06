import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutThreeLeafStarGraph
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation

/-!
# maxcut_three_leaf_star_no_fixed_profile_extension

Topic: equilibria   Node: 7b3de950d217

Provenance: helper lemma. Finite obstruction computed in experiment 16369.

The identity three-coloring is a strong equilibrium on three isolated vertices, but restoring a new center adjacent to all three cannot extend that same profile to a strong equilibrium using any of the three colors.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
instance : DecidableRel maxcut_three_leaf_star_graph.Adj := by
  unfold maxcut_three_leaf_star_graph
  infer_instance

theorem maxcut_three_leaf_star_no_fixed_profile_extension :
    is_maxcut_strong_equilibrium (⊥ : SimpleGraph (Fin 3)) (id : Fin 3 → Fin 3) ∧
    ∀ c : Fin 3, ¬ is_maxcut_strong_equilibrium maxcut_three_leaf_star_graph (Fin.cases c id) := by
  unfold is_maxcut_strong_equilibrium is_maxcut_strong_deviation maxcut_utility
  decide
