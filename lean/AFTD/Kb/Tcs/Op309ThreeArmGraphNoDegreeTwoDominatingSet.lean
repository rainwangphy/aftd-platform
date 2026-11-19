import AFTD.Prelude
import AFTD.Kb.Tcs.Op309ThreeArmGraph

/-!
# op309_three_arm_graph_no_degree_two_dominating_set

Topic: graphs   Node: 18fae07db2ea

Provenance: helper lemma. A finite refutation of the all-subcubic path-selection shortcut in the OP-309 campaign.

The three-arm tree has no totally edge-dominating set whose selected degree is at most two.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

local instance op309_three_arm_graph_decidable : DecidableRel op309_three_arm_graph.Adj := fun u v =>
  inferInstanceAs (Decidable
    (((u.val, v.val) ∈ ([(0,1), (1,2), (0,3), (3,6), (0,4), (4,5)] : List (ℕ × ℕ))) ∨
     ((v.val, u.val) ∈ ([(0,1), (1,2), (0,3), (3,6), (0,4), (4,5)] : List (ℕ × ℕ)))))

local instance op309_three_arm_line_decidable : DecidableRel op309_three_arm_graph.lineGraph.Adj := fun e f =>
  decidable_of_iff (e ≠ f ∧ ∃ v : Fin 7, v ∈ e.1 ∧ v ∈ f.1)
    SimpleGraph.lineGraph_adj_iff_exists.symm

theorem op309_three_arm_graph_no_degree_two_dominating_set :
    ¬ ∃ R : Finset op309_three_arm_graph.edgeSet,
      (∀ v : Fin 7, (R.filter fun e => v ∈ e.1).card ≤ 2) ∧
      (∀ e : op309_three_arm_graph.edgeSet,
        ∃ f ∈ R, op309_three_arm_graph.lineGraph.Adj e f) := by
  decide
