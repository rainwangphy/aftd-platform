import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutPinnedTwinsGraph
import AFTD.Kb.GameTheoryEconomics.MaxcutAnchorThreeInitialColoring
import AFTD.Kb.GameTheoryEconomics.MaxcutAnchorThreeStableColoring
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfare
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation

/-!
# maxcut_pinned_twins_displayed_deviation

Topic: equilibria   Node: 668a8cc4a4ad

Provenance: helper lemma. Concrete witness check for the new OP-89 pinned-twin construction. The computational quotient check is experiment 5022. Every core twin gains one utility unit; Lean checks the strong deviation and initial welfare directly on all 182 vertices.

The pinned-twin graph has an initial coloring of welfare 16376 and a strong deviation consisting of all 32 core twins to the doubled post-deviation coloring. This does not assert optimality or exclude other optimal colorings.
-/

private instance maxcut_pinned_twins_displayed_deviation_pinned_graph_decidable :
    DecidableRel maxcut_pinned_twins_graph.Adj := by
  unfold maxcut_pinned_twins_graph
  infer_instance

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 200000

private lemma maxcut_pinned_twins_displayed_deviation_welfare :
    maxcut_welfare maxcut_pinned_twins_graph
      (fun v => maxcut_anchor_three_initial_coloring v.1) = 16376 := by
  decide

private lemma maxcut_pinned_twins_displayed_deviation_strong :
    is_maxcut_strong_deviation maxcut_pinned_twins_graph
      (fun v => maxcut_anchor_three_initial_coloring v.1)
      (Finset.univ.filter fun v => v.1.isLeft)
      (fun v => maxcut_anchor_three_stable_coloring v.1) := by
  unfold is_maxcut_strong_deviation
  decide

theorem maxcut_pinned_twins_displayed_deviation :
    maxcut_welfare maxcut_pinned_twins_graph
      (fun v => maxcut_anchor_three_initial_coloring v.1) = 16376 ∧
    is_maxcut_strong_deviation maxcut_pinned_twins_graph
      (fun v => maxcut_anchor_three_initial_coloring v.1)
      (Finset.univ.filter fun v => v.1.isLeft)
      (fun v => maxcut_anchor_three_stable_coloring v.1) := ⟨maxcut_pinned_twins_displayed_deviation_welfare, maxcut_pinned_twins_displayed_deviation_strong⟩
