import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicFourBlockColNat
import AFTD.Kb.Tcs.CyclicFourBlockColBound

/-!
# cyclic_four_block_col

Topic: graphs   Node: 01e5f08881c5

Provenance: helper lemma. decomposition of cyclic_four_block_graph_exists_rich_neighbor_five_coloring (proof plan of the IN-156 scratch file)

Helper for cyclic_four_block_graph_exists_rich_neighbor_five_coloring: the periodic five-colouring of indexed edges, valued in Fin 5.
-/

def cyclic_four_block_col (m : ℕ) (e : (Fin (2*m+5) × Fin 6)) : Fin 5 :=
  ⟨cyclic_four_block_col_nat m e,cyclic_four_block_col_bound m e⟩
