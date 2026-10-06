import AFTD.Prelude
import AFTD.Kb.Tcs.GraphMatchingNum

/-!
# graph_matching_num_bot

Topic: graphs   Node: f90900af1815

Provenance: formalization of a published result. Source: standard textbook result (graph theory: the empty graph has matching number 0)

The matching number of the empty graph (bot) is 0.
-/

/-- The empty graph has matching number 0. -/
theorem graph_matching_num_bot {V : Type*} : graph_matching_num (⊥ : SimpleGraph V) = 0 := by
  unfold graph_matching_num
  apply le_antisymm
  · refine iSup_le fun M => iSup_le fun _ => ?_
    have h : M.edgeSet = ∅ :=
      Set.subset_empty_iff.mp (SimpleGraph.edgeSet_bot ▸ M.edgeSet_subset)
    rw [h, Set.encard_empty]
  · exact zero_le
