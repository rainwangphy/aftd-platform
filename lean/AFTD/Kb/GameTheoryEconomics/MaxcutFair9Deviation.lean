import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutFair9Graph
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation

/-!
# maxcut_fair9_deviation

Topic: equilibria   Node: 776e1590e5b7

Provenance: helper lemma. Nine-vertex finite obstruction to fair Nash selection in the OP-85 strong-equilibrium campaign, discovered in experiment 12959 and independently checked in 12961, 12964, and 12973.

The target profile is a strong deviation from the source profile using exactly the vertices whose colors change.
-/

private instance : DecidableRel maxcut_fair9_graph.Adj := by
  unfold maxcut_fair9_graph SimpleGraph.fromRel
  infer_instance

def maxcut_fair9_deviation (σ τ : Fin 9 → Fin 3) : Prop :=
  is_maxcut_strong_deviation maxcut_fair9_graph σ
    (Finset.univ.filter fun v => τ v ≠ σ v) τ
