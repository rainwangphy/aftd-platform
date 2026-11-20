import AFTD.Prelude
import AFTD.Kb.Tcs.Op309EightVertexWeightedPeelingChunk

/-!
# op309_eight_vertex_weighted_peeling_chunk_6

Topic: combinatorics   Node: 2c3ef06809f5

Provenance: helper lemma. OP-309 eight-vertex weighted peeling finite kernel, IN-1099.

The displayed incidence-weighted peeling check succeeds for catalog entries 60 through 69.
-/

theorem op309_eight_vertex_weighted_peeling_chunk_6 : op309_eight_vertex_weighted_peeling_chunk 60 = true := by
  set_option maxRecDepth 32768 in
    set_option maxHeartbeats 0 in
      decide
