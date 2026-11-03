import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph

/-!
# digraph_common_predecessor_double_edges

Topic: graphs   Node: d67c00669dad

Provenance: helper lemma. Triangle-free center budget for the four-cycle campaign.

The number of edges in the common-predecessor graph whose endpoints have exactly two common predecessors.
-/

noncomputable def digraph_common_predecessor_double_edges
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj] : ℕ := by
  classical
  exact ((digraph_common_predecessor_graph D).edgeFinset.filter fun e =>
    (Finset.univ.filter fun p => ∀ x, x ∈ e → D.Adj p x).card = 2).card
