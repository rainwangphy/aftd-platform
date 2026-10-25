import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicFourBlockNext
import AFTD.Kb.Tcs.CyclicFourBlockPrev

/-!
# cyclic_four_block_W

Topic: graphs   Node: 46ed91733d4f

Provenance: helper lemma. decomposition of cyclic_four_block_graph_exists_rich_neighbor_five_coloring (proof plan of the IN-156 scratch file)

Helper for cyclic_four_block_graph_exists_rich_neighbor_five_coloring: the chosen rich neighbour (a good adjacent edge) of each indexed edge.
-/

def cyclic_four_block_W (m : ℕ) (e : (Fin (2*m+5) × Fin 6)) : (Fin (2*m+5) × Fin 6) :=
  let i := e.1
  ![(i,(⟨1,by decide⟩ : Fin 6)),(i,(⟨2,by decide⟩ : Fin 6)),(i,(⟨1,by decide⟩ : Fin 6)),
    if i.val+1=(2*m+5) then (cyclic_four_block_prev m i,(⟨3,by decide⟩ : Fin 6))
    else if i.val=0 then (cyclic_four_block_next m i,(⟨0,by decide⟩ : Fin 6)) else (i,(⟨0,by decide⟩ : Fin 6)),
    (i,(⟨1,by decide⟩ : Fin 6)),(i,(⟨2,by decide⟩ : Fin 6))] e.2
