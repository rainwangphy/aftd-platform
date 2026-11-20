import AFTD.Prelude
import AFTD.Kb.Tcs.Op309EightVertexWeightedPeelingChunk

/-!
# op309_eight_vertex_weighted_peeling_chunk_2

Topic: combinatorics   Node: 25f289d18d8a

Provenance: helper lemma. OP-309 eight-vertex weighted peeling finite kernel, IN-1099.

The displayed incidence-weighted peeling check succeeds for catalog entries 20 through 29.
-/

theorem op309_eight_vertex_weighted_peeling_chunk_2 : op309_eight_vertex_weighted_peeling_chunk 20 = true := by
  set_option maxRecDepth 32768 in
    set_option maxHeartbeats 0 in
      decide
