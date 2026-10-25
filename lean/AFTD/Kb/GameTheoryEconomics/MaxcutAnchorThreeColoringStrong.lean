import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutAnchorThreeGraph
import AFTD.Kb.GameTheoryEconomics.MaxcutAnchorThreeStableColoring
import AFTD.Kb.GameTheoryEconomics.MaxcutStrongEquilibriumOfRankedNeighbors
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium

/-!
# maxcut_anchor_three_coloring_strong

Topic: equilibria   Node: 9fb2ae78daf3

Provenance: original. Related work: OP-89, arXiv:2610.04948 Secs. 2 and 4. The paper supplies G_3 and tau; this check adds a strong-equilibrium certificate for tau. It is a diagnostic example for the stable-optimum question and is not marked as a research advance.

The displayed post-deviation coloring tau is a strong equilibrium on the paper’s explicit graph G_3. This theorem proves stability only; optimality of the construction is not formalized here.
-/

private instance graph_decidable : DecidableRel maxcut_anchor_three_graph.Adj := by
  unfold maxcut_anchor_three_graph
  infer_instance

namespace MaxcutAnchorThree
private def rank : (Fin 16 ⊕ (Fin 3 × Fin 25)) → ℕ
  | .inl u => if 4 ≤ u.val ∧ u.val < 12 then 0 else 2
  | .inr (j, i) => if (j.val = 1 ∨ j.val = 2) ∧ i.val < 3 then 1 else 0

end MaxcutAnchorThree
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 200000

theorem maxcut_anchor_three_coloring_strong :
    @is_maxcut_strong_equilibrium _ _ maxcut_anchor_three_graph
      (by unfold maxcut_anchor_three_graph; infer_instance) 3
      maxcut_anchor_three_stable_coloring := by
  apply maxcut_strong_equilibrium_of_ranked_neighbors _ _ MaxcutAnchorThree.rank
  decide
