import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicFourBlockNext

/-!
# cyclic_four_block_dst

Topic: graphs   Node: 13e3c3e2cff7

Provenance: helper lemma. decomposition of cyclic_four_block_graph_exists_rich_neighbor_five_coloring (proof plan of the IN-156 scratch file)

Helper for cyclic_four_block_graph_exists_rich_neighbor_five_coloring: the second endpoint (as a natural number) of the indexed edge (i,j).
-/

def cyclic_four_block_dst (m : ℕ) (e : (Fin (2*m+5) × Fin 6)) : ℕ :=
  ![4*e.1.val+1,4*e.1.val+2,4*e.1.val+3,
    4*(cyclic_four_block_next m e.1).val+1,
    if e.1.val+1 = (2*m+5) then 3 else 4*(e.1.val+1)+2,
    if e.1.val+1 = (2*m+5) then 2 else 4*(e.1.val+1)+3] e.2
