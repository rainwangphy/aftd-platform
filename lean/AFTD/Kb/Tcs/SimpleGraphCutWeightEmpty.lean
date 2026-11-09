import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCutWeight
import AFTD.Kb.Tcs.TwoLeSimpleGraphTreeEstimate

/-!
# simple_graph_cut_weight_empty

Topic: graphs   Node: 3575f2267042

Provenance: helper lemma. folklore

In any simple graph G on a finite type V with decidable equality and decidable adjacency, with edge weighting w : G.edgeSet → ℝ, the cut weight simple_graph_cut_weight G w ∅ of the empty vertex set is zero.
-/

/-- The cut weight of the empty set of vertices is zero. -/
theorem simple_graph_cut_weight_empty {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : G.edgeSet → ℝ) :
    simple_graph_cut_weight G w ∅ = 0 := by first | exact two_le_simple_graph_tree_estimate | (apply two_le_simple_graph_tree_estimate <;> assumption) | (apply two_le_simple_graph_tree_estimate <;> simp_all) | simpa using two_le_simple_graph_tree_estimate | (simp only [simple_graph_cut_weight] at *; first | exact two_le_simple_graph_tree_estimate | (apply two_le_simple_graph_tree_estimate <;> assumption) | (apply two_le_simple_graph_tree_estimate <;> simp_all) | simpa using two_le_simple_graph_tree_estimate)
