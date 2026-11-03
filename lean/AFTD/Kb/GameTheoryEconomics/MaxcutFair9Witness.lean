import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutFair9Graph
import AFTD.Kb.GameTheoryEconomics.MaxcutFair9Colors
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_fair9_witness

Topic: equilibria   Node: 3d7ab076993d

Provenance: helper lemma. Nine-vertex finite obstruction to fair Nash selection in the OP-85 strong-equilibrium campaign, discovered in experiment 12959 and independently checked in 12961, 12964, and 12973.

A specified three-color profile on the nine-vertex graph has utility at least four for every vertex and admits no profitable singleton deviation.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 200000
private instance : DecidableRel maxcut_fair9_graph.Adj := by
  unfold maxcut_fair9_graph SimpleGraph.fromRel
  infer_instance

theorem maxcut_fair9_witness :
    (∀ v : Fin 9, 4 ≤ maxcut_utility maxcut_fair9_graph (maxcut_fair9_colors 1 2 2 1 2 1 0 0) v) ∧
    (∀ v : Fin 9, ∀ q : Fin 3,
      ¬ is_maxcut_strong_deviation maxcut_fair9_graph (maxcut_fair9_colors 1 2 2 1 2 1 0 0) {v}
        (Function.update (maxcut_fair9_colors 1 2 2 1 2 1 0 0) v q)) := by
  unfold is_maxcut_strong_deviation maxcut_utility
  decide +kernel
