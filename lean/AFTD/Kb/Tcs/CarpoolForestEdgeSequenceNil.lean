import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolForestEdgeSequence

/-!
# carpool_forest_edge_sequence_nil

Topic: online_algorithms   Node: 1946bc990374

Provenance: helper lemma. arXiv:2611.00388: Online carpooling against an oblivious adversary; OP-1106

The empty list of edges is an oblivious forest edge sequence on Fin n.
-/

/-- The empty edge sequence is a valid carpool forest edge sequence. -/
theorem carpool_forest_edge_sequence_nil (n : ℕ) :
    CarpoolForestEdgeSequence n [] := by
  dsimp [CarpoolForestEdgeSequence, ValidCarpoolEdgeSequence]
  refine ⟨by simp, List.nodup_nil, ?_⟩
  have h_empty : {x | ∃ e ∈ ([] : List (Fin n × Fin n)), s(e.1, e.2) = x} = ∅ := by
    ext x; simp
  rw [h_empty, SimpleGraph.fromEdgeSet_empty]
  exact SimpleGraph.isAcyclic_bot
