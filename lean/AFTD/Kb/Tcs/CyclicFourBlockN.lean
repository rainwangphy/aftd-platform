import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicFourBlockNext
import AFTD.Kb.Tcs.CyclicFourBlockPrev

/-!
# cyclic_four_block_N

Topic: graphs   Node: 72af2e87b007

Provenance: helper lemma. decomposition of cyclic_four_block_graph_exists_rich_neighbor_five_coloring (proof plan of the IN-156 scratch file)

Helper for cyclic_four_block_graph_exists_rich_neighbor_five_coloring: the four indexed edges adjacent to an indexed edge, listed by k : Fin 4.
-/

def cyclic_four_block_N (m : ℕ) (e : (Fin (2*m+5) × Fin 6)) (k : Fin 4) : (Fin (2*m+5) × Fin 6) :=
  let i := e.1
  ![![(i,(⟨1,by decide⟩ : Fin 6)),(i,(⟨2,by decide⟩ : Fin 6)),(cyclic_four_block_prev m i,(⟨3,by decide⟩ : Fin 6)),(i,(⟨3,by decide⟩ : Fin 6))],
    ![(i,(⟨0,by decide⟩ : Fin 6)),(i,(⟨2,by decide⟩ : Fin 6)),(cyclic_four_block_prev m i,if i.val=0 then (⟨5,by decide⟩ : Fin 6) else (⟨4,by decide⟩ : Fin 6)),(i,(⟨4,by decide⟩ : Fin 6))],
    ![(i,(⟨0,by decide⟩ : Fin 6)),(i,(⟨1,by decide⟩ : Fin 6)),(cyclic_four_block_prev m i,if i.val=0 then (⟨4,by decide⟩ : Fin 6) else (⟨5,by decide⟩ : Fin 6)),(i,(⟨5,by decide⟩ : Fin 6))],
    ![(i,(⟨0,by decide⟩ : Fin 6)),(cyclic_four_block_prev m i,(⟨3,by decide⟩ : Fin 6)),(cyclic_four_block_next m i,(⟨0,by decide⟩ : Fin 6)),(cyclic_four_block_next m i,(⟨3,by decide⟩ : Fin 6))],
    ![(i,(⟨1,by decide⟩ : Fin 6)),(cyclic_four_block_prev m i,if i.val=0 then (⟨5,by decide⟩ : Fin 6) else (⟨4,by decide⟩ : Fin 6)),
      (cyclic_four_block_next m i,if i.val+1=(2*m+5) then (⟨2,by decide⟩ : Fin 6) else (⟨1,by decide⟩ : Fin 6)),
      (cyclic_four_block_next m i,if i.val+1=(2*m+5) then (⟨5,by decide⟩ : Fin 6) else (⟨4,by decide⟩ : Fin 6))],
    ![(i,(⟨2,by decide⟩ : Fin 6)),(cyclic_four_block_prev m i,if i.val=0 then (⟨4,by decide⟩ : Fin 6) else (⟨5,by decide⟩ : Fin 6)),
      (cyclic_four_block_next m i,if i.val+1=(2*m+5) then (⟨1,by decide⟩ : Fin 6) else (⟨2,by decide⟩ : Fin 6)),
      (cyclic_four_block_next m i,if i.val+1=(2*m+5) then (⟨4,by decide⟩ : Fin 6) else (⟨5,by decide⟩ : Fin 6))]] e.2 k
