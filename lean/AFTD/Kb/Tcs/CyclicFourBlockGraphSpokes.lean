import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicFourBlockGraph

/-!
# cyclic_four_block_graph_spokes

Topic: graphs   Node: 1e599b8d66a7

Provenance: helper lemma. Sanity lemma for cyclic_four_block_graph, the explicit family used for the OP-309 partial case.

Each central vertex of cyclic_four_block_graph is adjacent to its three outer vertices.
-/

theorem cyclic_four_block_graph_spokes (m : ℕ) (i : Fin (2*m+5)) (j : Fin 3) :
    (cyclic_four_block_graph m).Adj
      ⟨4*i.val,by omega⟩ ⟨4*i.val+j.val+1,by omega⟩ := by
  dsimp only [cyclic_four_block_graph]
  rw [SimpleGraph.fromEdgeSet_adj]
  refine ⟨⟨(i,j.castAdd 3),?_⟩,?_⟩
  · fin_cases j <;> rfl
  · intro h
    have hv := congrArg Fin.val h
    dsimp at hv
    omega
