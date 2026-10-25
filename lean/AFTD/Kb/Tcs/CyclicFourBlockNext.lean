import AFTD.Prelude

/-!
# cyclic_four_block_next

Topic: graphs   Node: 714650014712

Provenance: helper lemma. decomposition of cyclic_four_block_graph_exists_rich_neighbor_five_coloring (proof plan of the IN-156 scratch file)

Helper for cyclic_four_block_graph_exists_rich_neighbor_five_coloring: the next block index i+1, cyclically mod n=2m+5.
-/

def cyclic_four_block_next (m : ℕ) (i : Fin ((2*m+5))) : Fin ((2*m+5)) :=
  ⟨if i.val+1 < (2*m+5) then i.val+1 else 0, by split_ifs <;> omega⟩
