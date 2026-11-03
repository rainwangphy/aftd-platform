import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutFair9Graph
import AFTD.Kb.GameTheoryEconomics.MaxcutFair9Colors
import AFTD.Kb.GameTheoryEconomics.MaxcutStrongEquilibriumOfRankedNeighbors
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium

/-!
# maxcut_fair9_stable_example

Topic: equilibria   Node: 0875f6419757

Provenance: helper lemma. Nine-vertex finite obstruction to fair Nash selection in the OP-85 strong-equilibrium campaign, discovered in experiment 12959 and independently checked in 12961, 12964, and 12973.

A specified three-color profile is a strong equilibrium of the nine-vertex graph.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 200000
private instance : DecidableRel maxcut_fair9_graph.Adj := by
  unfold maxcut_fair9_graph SimpleGraph.fromRel
  infer_instance

theorem maxcut_fair9_stable_example :
    is_maxcut_strong_equilibrium maxcut_fair9_graph (maxcut_fair9_colors 1 1 2 0 1 0 2 0) := by
  apply maxcut_strong_equilibrium_of_ranked_neighbors maxcut_fair9_graph _
    (fun v => if v.val = 4 ∨ v.val = 8 then 1 else 0)
  decide +kernel
