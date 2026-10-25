import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicFourBlockNext
import AFTD.Kb.Tcs.CyclicFourBlockSrc
import AFTD.Kb.Tcs.CyclicFourBlockDst
import AFTD.Kb.Tcs.CyclicFourBlockEdge

/-!
# cyclic_four_block_nondiag

Topic: graphs   Node: 73189305c6b9

Provenance: helper lemma. decomposition of cyclic_four_block_graph_exists_rich_neighbor_five_coloring

Step of cyclic_four_block_graph_exists_rich_neighbor_five_coloring: nondiag.
-/

theorem cyclic_four_block_nondiag (m : ℕ) (e : (Fin (2*m+5) × Fin 6)) :
    ¬ (cyclic_four_block_edge m e).IsDiag := by
  simp only [cyclic_four_block_edge,Sym2.mk_isDiag_iff,Fin.mk.injEq]
  rcases e with ⟨i,j⟩
  have hi := i.isLt
  skip
  fin_cases j <;> dsimp [cyclic_four_block_src,cyclic_four_block_dst,cyclic_four_block_next]
  all_goals (try split_ifs) <;> omega
