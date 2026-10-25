import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicFourBlockSrc
import AFTD.Kb.Tcs.CyclicFourBlockDst
import AFTD.Kb.Tcs.CyclicFourBlockBounds

/-!
# cyclic_four_block_edge

Topic: graphs   Node: d00035b1d9ec

Provenance: helper lemma. decomposition of cyclic_four_block_graph_exists_rich_neighbor_five_coloring (proof plan of the IN-156 scratch file)

Helper for cyclic_four_block_graph_exists_rich_neighbor_five_coloring: the indexed edge (i,j) of cyclic_four_block_graph m as an unordered pair of vertices.
-/

def cyclic_four_block_edge (m : ℕ) (e : (Fin (2*m+5) × Fin 6)) : Sym2 (Fin (4*(2*m+5))) :=
  s(⟨cyclic_four_block_src m e,(cyclic_four_block_bounds m e).1⟩,⟨cyclic_four_block_dst m e,(cyclic_four_block_bounds m e).2⟩)
