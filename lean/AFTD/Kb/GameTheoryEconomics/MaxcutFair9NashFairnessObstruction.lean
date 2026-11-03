import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutFair9Graph
import AFTD.Kb.GameTheoryEconomics.MaxcutFair9Colors
import AFTD.Kb.GameTheoryEconomics.MaxcutFair9Witness
import AFTD.Kb.GameTheoryEconomics.MaxcutFair9NoStrongWithMinFour
import AFTD.Kb.GameTheoryEconomics.MaxcutFair9StableExample
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_fair9_nash_fairness_obstruction

Topic: equilibria   Node: 1178420c13e2

Provenance: original. Related work: Nine-vertex finite obstruction to fair Nash selection in the OP-85 strong-equilibrium campaign, discovered in experiment 12959 and independently checked in 12961, 12964, and 12973.

On the specified nine-vertex three-color graph there is a singleton-stable profile with every utility at least four, no strong equilibrium has every utility at least four, and a strong equilibrium exists.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 200000
private instance : DecidableRel maxcut_fair9_graph.Adj := by
  unfold maxcut_fair9_graph SimpleGraph.fromRel
  infer_instance

theorem maxcut_fair9_nash_fairness_obstruction :
    (∃ σ : Fin 9 → Fin 3,
      (∀ v : Fin 9, 4 ≤ maxcut_utility maxcut_fair9_graph σ v) ∧
      (∀ v : Fin 9, ∀ q : Fin 3, ¬ is_maxcut_strong_deviation maxcut_fair9_graph σ {v} (Function.update σ v q))) ∧
    (∀ σ : Fin 9 → Fin 3, (∀ v : Fin 9, 4 ≤ maxcut_utility maxcut_fair9_graph σ v) →
      ¬ is_maxcut_strong_equilibrium maxcut_fair9_graph σ) ∧
    ∃ σ : Fin 9 → Fin 3, is_maxcut_strong_equilibrium maxcut_fair9_graph σ := by
  refine ⟨⟨maxcut_fair9_colors 1 2 2 1 2 1 0 0, maxcut_fair9_witness⟩,
    maxcut_fair9_no_strong_with_min_four, ?_⟩
  exact ⟨maxcut_fair9_colors 1 1 2 0 1 0 2 0, maxcut_fair9_stable_example⟩
