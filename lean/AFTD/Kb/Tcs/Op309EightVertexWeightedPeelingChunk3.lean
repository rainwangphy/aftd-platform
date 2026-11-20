import AFTD.Prelude
import AFTD.Kb.Tcs.Op309EightVertexWeightedPeelingChunk

/-!
# op309_eight_vertex_weighted_peeling_chunk_3

Topic: combinatorics   Node: eb71498ae464

Provenance: helper lemma. OP-309 eight-vertex weighted peeling finite kernel, IN-1099.

The displayed incidence-weighted peeling check succeeds for catalog entries 30 through 39.
-/

theorem op309_eight_vertex_weighted_peeling_chunk_3 : op309_eight_vertex_weighted_peeling_chunk 30 = true := by
  set_option maxRecDepth 32768 in
    set_option maxHeartbeats 0 in
      decide
