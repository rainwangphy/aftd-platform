import AFTD.Prelude

/-!
# cyclic_four_block_col_nat

Topic: graphs   Node: a7d39919f03b

Provenance: helper lemma. decomposition of cyclic_four_block_graph_exists_rich_neighbor_five_coloring (proof plan of the IN-156 scratch file)

Helper for cyclic_four_block_graph_exists_rich_neighbor_five_coloring: the periodic five-colour assignment to indexed edges, as a natural number.
-/

def cyclic_four_block_col_nat (m : ℕ) (e : (Fin (2*m+5) × Fin 6)) : ℕ :=
  if e.1.val+1 = (2*m+5) then ![2,1,0,1,3,4] e.2
  else if e.1.val % 2 = 0 then ![0,1,2,3,3,4] e.2
  else ![0,1,2,4,4,3] e.2
