import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicFourBlockNext
import AFTD.Kb.Tcs.CyclicFourBlockPrev
import AFTD.Kb.Tcs.CyclicFourBlockSrc
import AFTD.Kb.Tcs.CyclicFourBlockDst
import AFTD.Kb.Tcs.CyclicFourBlockEdge
import AFTD.Kb.Tcs.CyclicFourBlockTouch
import AFTD.Kb.Tcs.CyclicFourBlockGood
import AFTD.Kb.Tcs.CyclicFourBlockW

/-!
# cyclic_four_block_witness

Topic: graphs   Node: 08b0d384009c

Provenance: helper lemma. decomposition of cyclic_four_block_graph_exists_rich_neighbor_five_coloring

Step of cyclic_four_block_graph_exists_rich_neighbor_five_coloring: witness.
-/

theorem cyclic_four_block_witness (m : ℕ) (e : (Fin (2*m+5) × Fin 6)) :
    cyclic_four_block_edge m e ≠ cyclic_four_block_edge m (cyclic_four_block_W m e) ∧
    cyclic_four_block_touch m e (cyclic_four_block_W m e) ∧ cyclic_four_block_good m (cyclic_four_block_W m e) := by
  rcases e with ⟨i,j⟩
  have hi := i.isLt
  skip
  fin_cases j
  all_goals simp only [ne_eq,cyclic_four_block_edge,Sym2.eq_iff,Prod.mk.injEq,Fin.mk.injEq]
  all_goals dsimp [cyclic_four_block_W,cyclic_four_block_touch,cyclic_four_block_good,cyclic_four_block_src,cyclic_four_block_dst,cyclic_four_block_next,cyclic_four_block_prev]
  all_goals try simp only [Fin.mk.injEq,Fin.ext_iff]
  all_goals try simp only [and_true,and_false,or_true,or_false,true_and,false_and,true_or,false_or,not_true_eq_false,not_false_eq_true] at *
  all_goals first | omega | (
    (try split_ifs at *) <;> (try dsimp at *) <;>
    (try simp only [Prod.mk.injEq,Fin.mk.injEq,Fin.ext_iff] at *) <;>
    (try simp only [and_true,and_false,or_true,or_false,true_and,false_and,true_or,false_or,not_true_eq_false,not_false_eq_true] at *) <;>
    first | omega | (
      (try split_ifs at *) <;> (try dsimp at *) <;>
      (try simp only [Prod.mk.injEq,Fin.mk.injEq,Fin.ext_iff] at *) <;>
      (try simp only [and_true,and_false,or_true,or_false,true_and,false_and,true_or,false_or,not_true_eq_false,not_false_eq_true] at *) <;>
      first | omega | (
        (try split_ifs at *) <;> (try dsimp at *) <;>
        (try simp only [Prod.mk.injEq,Fin.mk.injEq,Fin.ext_iff] at *) <;>
        (try simp only [and_true,and_false,or_true,or_false,true_and,false_and,true_or,false_or,not_true_eq_false,not_false_eq_true] at *) <;> omega)))
