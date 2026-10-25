import AFTD.Prelude

/-!
# cyclic_four_block_good

Topic: graphs   Node: 185fa89cde77

Provenance: helper lemma. decomposition of cyclic_four_block_graph_exists_rich_neighbor_five_coloring (proof plan of the IN-156 scratch file)

Helper for cyclic_four_block_graph_exists_rich_neighbor_five_coloring: the indexed edges whose four neighbouring edges receive four distinct colours.
-/

def cyclic_four_block_good (m : ℕ) (e : (Fin (2*m+5) × Fin 6)) : Prop :=
  e.2.val = 1 ∨ e.2.val = 2 ∨ (e.2.val = 0 ∧ 0<e.1.val ∧ e.1.val+1 < (2*m+5)) ∨
    (e.2.val = 3 ∧ e.1.val+2=(2*m+5))
