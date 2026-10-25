import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicFourBlockColNat

/-!
# cyclic_four_block_col_bound

Topic: graphs   Node: 834363118bdc

Provenance: helper lemma. decomposition of cyclic_four_block_graph_exists_rich_neighbor_five_coloring

Step of cyclic_four_block_graph_exists_rich_neighbor_five_coloring: col bound.
-/

theorem cyclic_four_block_col_bound (m : ℕ) (e : (Fin (2*m+5) × Fin 6)) : cyclic_four_block_col_nat m e < 5 := by
  rcases e with ⟨i,j⟩
  fin_cases j <;> dsimp [cyclic_four_block_col_nat]
  all_goals split_ifs <;> omega
