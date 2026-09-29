import AFTD.Prelude
import AFTD.Kb.Tcs.GraphMatchingNum

/-!
# graph_matching_num_le_encard_edgeSet

Topic: graphs   Node: 40410d6e55fc

In any simple graph G, the matching number is at most the cardinality of the edge set.
-/

/-- The matching number of a simple graph is at most the cardinality of its edge set. -/
theorem graph_matching_num_le_encard_edgeSet {V : Type*} (G : SimpleGraph V) :
    graph_matching_num G ≤ G.edgeSet.encard := by
  unfold graph_matching_num
  exact iSup_le fun M => iSup_le fun _ => Set.encard_le_encard M.edgeSet_subset
