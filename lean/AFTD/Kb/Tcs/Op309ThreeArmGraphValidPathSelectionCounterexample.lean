import AFTD.Prelude
import AFTD.Kb.Tcs.Op309ThreeArmGraph
import AFTD.Kb.Tcs.Op309ThreeArmGraphNoDegreeTwoDominatingSet

/-!
# op309_three_arm_graph_valid_path_selection_counterexample

Topic: graphs   Node: 126b0567024c

Provenance: helper lemma. A concrete path-selection obstruction for the OP-309 subcubic coloring campaign.

The displayed seven-vertex graph is connected and subcubic, is not the complete graph on four vertices, and has no totally edge-dominating set with selected degree at most two.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

local instance op309_three_arm_graph_valid_decidable : DecidableRel op309_three_arm_graph.Adj := fun u v =>
  inferInstanceAs (Decidable
    (((u.val, v.val) ∈ ([(0,1), (1,2), (0,3), (3,6), (0,4), (4,5)] : List (ℕ × ℕ))) ∨
     ((v.val, u.val) ∈ ([(0,1), (1,2), (0,3), (3,6), (0,4), (4,5)] : List (ℕ × ℕ)))))

theorem op309_three_arm_graph_valid_path_selection_counterexample :
    op309_three_arm_graph.Connected ∧ op309_three_arm_graph.maxDegree ≤ 3 ∧
    IsEmpty (op309_three_arm_graph ≃g (⊤ : SimpleGraph (Fin 4))) ∧
    ¬ ∃ R : Finset op309_three_arm_graph.edgeSet,
      (∀ v : Fin 7, (R.filter fun e => v ∈ e.1).card ≤ 2) ∧
      (∀ e : op309_three_arm_graph.edgeSet,
        ∃ f ∈ R, op309_three_arm_graph.lineGraph.Adj e f) := by
  refine ⟨?_, ?_, ?_, op309_three_arm_graph_no_degree_two_dominating_set⟩
  · decide
  · decide
  · constructor
    intro h
    have hc := Fintype.card_congr h.toEquiv
    norm_num at hc
