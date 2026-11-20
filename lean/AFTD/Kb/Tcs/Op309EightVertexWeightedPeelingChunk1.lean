import AFTD.Prelude
import AFTD.Kb.Tcs.Op309EightVertexWeightedPeelingChunk

/-!
# op309_eight_vertex_weighted_peeling_chunk_1

Topic: combinatorics   Node: b5cc4f19b326

Provenance: helper lemma. OP-309 eight-vertex weighted peeling finite kernel, IN-1099.

The displayed incidence-weighted peeling check succeeds for catalog entries 10 through 19.
-/

theorem op309_eight_vertex_weighted_peeling_chunk_1 : op309_eight_vertex_weighted_peeling_chunk 10 = true := by
  set_option maxRecDepth 32768 in
    set_option maxHeartbeats 0 in
      decide
