import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutFair9Graph
import AFTD.Kb.GameTheoryEconomics.MaxcutFair9Colors
import AFTD.Kb.GameTheoryEconomics.MaxcutFair9Targets
import AFTD.Kb.GameTheoryEconomics.MaxcutFair9Deviation
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_fair9_normalized_certificates

Topic: equilibria   Node: 753c3d02adfa

Provenance: helper lemma. Nine-vertex finite obstruction to fair Nash selection in the OP-85 strong-equilibrium campaign, discovered in experiment 12959 and independently checked in 12961, 12964, and 12973.

For every three-color profile on the nine-vertex graph whose first vertex has color zero, if all utilities are at least four and no singleton can profitably deviate, one of the six specified target profiles is a strong deviation.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 200000
private instance : DecidableRel maxcut_fair9_graph.Adj := by
  unfold maxcut_fair9_graph SimpleGraph.fromRel
  infer_instance
private instance (σ τ : Fin 9 → Fin 3) (S : Finset (Fin 9)) :
    Decidable (is_maxcut_strong_deviation maxcut_fair9_graph σ S τ) := by
  unfold is_maxcut_strong_deviation maxcut_utility
  infer_instance

private instance (σ τ : Fin 9 → Fin 3) : Decidable (maxcut_fair9_deviation σ τ) := by
  unfold maxcut_fair9_deviation is_maxcut_strong_deviation maxcut_utility
  infer_instance

theorem maxcut_fair9_normalized_certificates : ∀ a b c d e f g h : Fin 3,
    let σ := maxcut_fair9_colors a b c d e f g h
    (∀ v : Fin 9, 4 ≤ maxcut_utility maxcut_fair9_graph σ v) →
    (∀ v : Fin 9, ∀ q : Fin 3,
      ¬ is_maxcut_strong_deviation maxcut_fair9_graph σ {v} (Function.update σ v q)) →
    maxcut_fair9_targets.any (fun τ => decide (maxcut_fair9_deviation σ τ)) = true := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide +kernel
