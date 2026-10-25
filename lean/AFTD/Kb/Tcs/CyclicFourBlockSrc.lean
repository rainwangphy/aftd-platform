import AFTD.Prelude

/-!
# cyclic_four_block_src

Topic: graphs   Node: 63b608e2e455

Provenance: helper lemma. decomposition of cyclic_four_block_graph_exists_rich_neighbor_five_coloring (proof plan of the IN-156 scratch file)

Helper for cyclic_four_block_graph_exists_rich_neighbor_five_coloring: the first endpoint (as a natural number) of the indexed edge (i,j) of cyclic_four_block_graph m.
-/

def cyclic_four_block_src (m : ℕ) (e : (Fin (2*m+5) × Fin 6)) : ℕ :=
  4*e.1.val + ![0,0,0,1,2,3] e.2
