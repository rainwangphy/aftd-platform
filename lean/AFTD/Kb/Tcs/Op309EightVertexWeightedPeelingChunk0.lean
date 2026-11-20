import AFTD.Prelude
import AFTD.Kb.Tcs.Op309EightVertexWeightedPeelingChunk

/-!
# op309_eight_vertex_weighted_peeling_chunk_0

Topic: combinatorics   Node: 5bdf8f054447

Provenance: helper lemma. OP-309 eight-vertex weighted peeling finite kernel, IN-1099.

The displayed incidence-weighted peeling check succeeds for catalog entries 0 through 9.
-/

theorem op309_eight_vertex_weighted_peeling_chunk_0 : op309_eight_vertex_weighted_peeling_chunk 0 = true := by
  set_option maxRecDepth 32768 in
    set_option maxHeartbeats 0 in
      decide
