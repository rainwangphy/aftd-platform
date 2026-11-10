import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutAnchorNeutralPivotGraph
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle71FirstDeviationMinimal
import AFTD.Kb.GameTheoryEconomics.MaxcutAnchorThreeInitialColoring
import AFTD.Kb.GameTheoryEconomics.MaxcutStrongEquilibriumOfRankedNeighbors
import AFTD.Kb.GameTheoryEconomics.MaxcutAnchorThreeGraph

/-!
# maxcut_anchor_neutral_pivot_initial_strong

Topic: equilibria   Node: d4e9f442a4a3

Provenance: helper lemma. Independent SAT and CP-SAT checks 16812 and 16814.

The displayed initial profile is a strong equilibrium after the extra edge is added.
-/

instance : DecidableRel maxcut_anchor_neutral_pivot_graph.Adj := by
  unfold maxcut_anchor_neutral_pivot_graph maxcut_anchor_three_graph
  infer_instance

set_option maxHeartbeats 1000000

private def maxcut_anchor_neutral_pivot_initial_rank : (Fin 16 ⊕ (Fin 3 × Fin 25)) → ℕ
  | Sum.inl u =>
    match u.val with
    | 0 => 2
    | 5 | 6 | 7 => 3
    | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 => 4
    | _ => 5
  | Sum.inr (j, i) =>
    if (j.val = 1 ∧ i.val = 0) ∨ (j.val = 2 ∧ i.val = 0) then 1 else 0

theorem maxcut_anchor_neutral_pivot_initial_strong : is_maxcut_strong_equilibrium maxcut_anchor_neutral_pivot_graph maxcut_anchor_three_initial_coloring := by
  apply maxcut_strong_equilibrium_of_ranked_neighbors _ _ maxcut_anchor_neutral_pivot_initial_rank
  decide
