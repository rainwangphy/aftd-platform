import AFTD.Prelude
import AFTD.Kb.Tcs.Op309EightVertexWeightedPeelingChunk

/-!
# op309_eight_vertex_weighted_peeling_chunk_4

Topic: combinatorics   Node: 6b95f6747c21

Provenance: helper lemma. OP-309 eight-vertex weighted peeling finite kernel, IN-1099.

The displayed incidence-weighted peeling check succeeds for catalog entries 40 through 49.
-/

theorem op309_eight_vertex_weighted_peeling_chunk_4 : op309_eight_vertex_weighted_peeling_chunk 40 = true := by
  set_option maxRecDepth 32768 in
    set_option maxHeartbeats 0 in
      decide
