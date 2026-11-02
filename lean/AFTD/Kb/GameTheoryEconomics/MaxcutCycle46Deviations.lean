import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle46Graph
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle46Coloring
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_cycle46_deviations

Topic: equilibria   Node: f70e4cae4817

Provenance: helper lemma. Concrete finite certificate for maxcut_unweighted_strong_deviation_cycle_exists, found via experiments 12434, 12437 and 12438.

Each successive pair of the five displayed colorings, including the transition from the fifth to the first, is a strong deviation on the 46-vertex graph, with coalition exactly the vertices whose colors change.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 200000

theorem maxcut_cycle46_deviations :
    ∀ i : Fin 5,
      @is_maxcut_strong_deviation _ _ maxcut_cycle46_graph
        (by unfold maxcut_cycle46_graph; infer_instance) 3
        (maxcut_cycle46_coloring i)
        (Finset.univ.filter fun v => maxcut_cycle46_coloring (i + 1) v ≠ maxcut_cycle46_coloring i v)
        (maxcut_cycle46_coloring (i + 1)) := by
  intro i
  fin_cases i <;> unfold is_maxcut_strong_deviation <;> decide
