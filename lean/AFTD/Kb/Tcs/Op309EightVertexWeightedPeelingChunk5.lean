import AFTD.Prelude
import AFTD.Kb.Tcs.Op309EightVertexWeightedPeelingChunk

/-!
# op309_eight_vertex_weighted_peeling_chunk_5

Topic: combinatorics   Node: 751f400a247c

Provenance: helper lemma. OP-309 eight-vertex weighted peeling finite kernel, IN-1099.

The displayed incidence-weighted peeling check succeeds for catalog entries 50 through 59.
-/

theorem op309_eight_vertex_weighted_peeling_chunk_5 : op309_eight_vertex_weighted_peeling_chunk 50 = true := by
  set_option maxRecDepth 32768 in
    set_option maxHeartbeats 0 in
      decide
