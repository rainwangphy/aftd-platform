import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicFourBlockNext
import AFTD.Kb.Tcs.CyclicFourBlockSrc
import AFTD.Kb.Tcs.CyclicFourBlockDst

/-!
# cyclic_four_block_bounds

Topic: graphs   Node: bc4094c4a591

Provenance: helper lemma. decomposition of cyclic_four_block_graph_exists_rich_neighbor_five_coloring

Step of cyclic_four_block_graph_exists_rich_neighbor_five_coloring: bounds.
-/

theorem cyclic_four_block_bounds (m : ℕ) (e : (Fin (2*m+5) × Fin 6)) :
    cyclic_four_block_src m e < 4*(2*m+5) ∧ cyclic_four_block_dst m e < 4*(2*m+5) := by
  rcases e with ⟨i,j⟩
  fin_cases j <;> dsimp [cyclic_four_block_src,cyclic_four_block_dst,cyclic_four_block_next]
  all_goals (try split_ifs) <;> omega
