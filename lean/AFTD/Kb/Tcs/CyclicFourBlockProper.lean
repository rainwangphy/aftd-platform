import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicFourBlockNext
import AFTD.Kb.Tcs.CyclicFourBlockSrc
import AFTD.Kb.Tcs.CyclicFourBlockDst
import AFTD.Kb.Tcs.CyclicFourBlockEdge
import AFTD.Kb.Tcs.CyclicFourBlockTouch
import AFTD.Kb.Tcs.CyclicFourBlockColNat
import AFTD.Kb.Tcs.CyclicFourBlockCol

/-!
# cyclic_four_block_proper

Topic: graphs   Node: a63cb9919edd

Provenance: helper lemma. decomposition of cyclic_four_block_graph_exists_rich_neighbor_five_coloring

Step of cyclic_four_block_graph_exists_rich_neighbor_five_coloring: proper.
-/

theorem cyclic_four_block_proper (m : ℕ) (e f : (Fin (2*m+5) × Fin 6))
    (hne : cyclic_four_block_edge m e ≠ cyclic_four_block_edge m f) (ht : cyclic_four_block_touch m e f) :
    cyclic_four_block_col m e ≠ cyclic_four_block_col m f := by
  intro hc
  have hcv := congrArg Fin.val hc
  clear hc
  rcases e with ⟨i,j⟩
  rcases f with ⟨k,l⟩
  have hi := i.isLt
  have hk := k.isLt
  skip
  fin_cases j <;> fin_cases l
  all_goals simp only [ne_eq,cyclic_four_block_edge,Sym2.eq_iff,Prod.mk.injEq,Fin.mk.injEq] at hne
  all_goals dsimp [cyclic_four_block_touch,cyclic_four_block_src,cyclic_four_block_dst,cyclic_four_block_col,cyclic_four_block_col_nat,cyclic_four_block_next] at ht hcv hne
  all_goals first | omega | ((try split_ifs at *) <;> (try dsimp at *) <;> omega)
