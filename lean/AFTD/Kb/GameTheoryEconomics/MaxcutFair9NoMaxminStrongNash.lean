import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutFair9Graph
import AFTD.Kb.GameTheoryEconomics.MaxcutFair9Colors
import AFTD.Kb.GameTheoryEconomics.MaxcutFair9Witness
import AFTD.Kb.GameTheoryEconomics.MaxcutFair9NoStrongWithMinFour
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation

/-!
# maxcut_fair9_no_maxmin_strong_nash

Topic: equilibria   Node: 596ce2ae4d75

Provenance: helper lemma. A consequence of the nine-vertex finite obstruction to max-min Nash selection in the OP-85 campaign, related to arXiv:2610.04948, Section 4.

On the specified nine-vertex graph, no strong equilibrium has minimum utility at least that of every singleton-stable three-coloring.
-/

private instance : DecidableRel maxcut_fair9_graph.Adj := by
  unfold maxcut_fair9_graph SimpleGraph.fromRel
  infer_instance

theorem maxcut_fair9_no_maxmin_strong_nash :
    ¬ ∃ σ : Fin 9 → Fin 3,
      is_maxcut_strong_equilibrium maxcut_fair9_graph σ ∧
      ∀ τ : Fin 9 → Fin 3,
        (∀ v : Fin 9, ∀ q : Fin 3, ¬ is_maxcut_strong_deviation maxcut_fair9_graph τ {v} (Function.update τ v q)) →
        ∀ m : ℕ, (∀ v : Fin 9, m ≤ maxcut_utility maxcut_fair9_graph τ v) →
          (∀ v : Fin 9, m ≤ maxcut_utility maxcut_fair9_graph σ v) := by
  rintro ⟨σ, hσ, h⟩
  exact maxcut_fair9_no_strong_with_min_four σ
    (h (maxcut_fair9_colors 1 2 2 1 2 1 0 0) maxcut_fair9_witness.2 4 maxcut_fair9_witness.1)
    hσ
