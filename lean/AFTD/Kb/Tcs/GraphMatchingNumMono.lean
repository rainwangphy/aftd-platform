import AFTD.Prelude
import AFTD.Kb.Tcs.GraphMatchingNum

/-!
# graph_matching_num_mono

Topic: graphs   Node: 4c617425702a

If G and G' are simple graphs on the same vertex set with G ≤ G', then the matching number of G is at most the matching number of G'.
-/

/-- The matching number of a subgraph is at most that of the supergraph. -/
theorem graph_matching_num_mono {V : Type*} {G G' : SimpleGraph V} (h : G ≤ G') :
    graph_matching_num G ≤ graph_matching_num G' := by
  unfold graph_matching_num
  refine iSup_le fun M => iSup_le fun hM => ?_
  have hM' : (M.map (SimpleGraph.Hom.ofLE h)).IsMatching := hM.map_ofLE h
  have hedge : (M.map (SimpleGraph.Hom.ofLE h)).edgeSet = M.edgeSet := by
    rw [SimpleGraph.Subgraph.edgeSet_map]
    have : (Sym2.map (SimpleGraph.Hom.ofLE h : V → V) : Sym2 V → Sym2 V) = id := by ext ⟨a, b⟩; rfl
    rw [this, Set.image_id]
  rw [← hedge]
  exact le_iSup_of_le (M.map (SimpleGraph.Hom.ofLE h)) (le_iSup_of_le hM' le_rfl)
