import AFTD.Prelude

/-!
# cyclic_four_block_prev

Topic: graphs   Node: 550319fe62d8

Provenance: helper lemma. decomposition of cyclic_four_block_graph_exists_rich_neighbor_five_coloring (proof plan of the IN-156 scratch file)

Helper for cyclic_four_block_graph_exists_rich_neighbor_five_coloring: the previous block index i-1, cyclically mod n=2m+5.
-/

def cyclic_four_block_prev (m : ℕ) (i : Fin ((2*m+5))) : Fin ((2*m+5)) :=
  ⟨if i.val = 0 then (2*m+5)-1 else i.val-1, by split_ifs <;> omega⟩
