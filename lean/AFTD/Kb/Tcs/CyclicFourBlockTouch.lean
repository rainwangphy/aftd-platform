import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicFourBlockSrc
import AFTD.Kb.Tcs.CyclicFourBlockDst

/-!
# cyclic_four_block_touch

Topic: graphs   Node: ec7298a03d5b

Provenance: helper lemma. decomposition of cyclic_four_block_graph_exists_rich_neighbor_five_coloring (proof plan of the IN-156 scratch file)

Helper for cyclic_four_block_graph_exists_rich_neighbor_five_coloring: two indexed edges share an endpoint (comparison of src/dst values).
-/

def cyclic_four_block_touch (m : ℕ) (e f : (Fin (2*m+5) × Fin 6)) : Prop :=
  cyclic_four_block_src m e = cyclic_four_block_src m f ∨ cyclic_four_block_src m e = cyclic_four_block_dst m f ∨
  cyclic_four_block_dst m e = cyclic_four_block_src m f ∨ cyclic_four_block_dst m e = cyclic_four_block_dst m f
