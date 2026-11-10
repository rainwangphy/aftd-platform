import AFTD.Prelude
import AFTD.Kb.Tcs.In715DeficitPSize
import AFTD.Kb.Tcs.In701PackingLeEdgeCover
import AFTD.Kb.Tcs.In715DeficitPTri
import AFTD.Kb.Tcs.In715DeficitPDisj
import AFTD.Kb.Tcs.In715DeficitCSize
import AFTD.Kb.Tcs.In715DeficitCEdges
import AFTD.Kb.Tcs.In715DeficitCover
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# in715_deficit_pack_eq

Topic: graphs   Node: 54ed0daaa641

Provenance: helper lemma. Finite graph and certificates from experiments 20940 and 20968; see state/campaigns/triangle_reductions/outside_induced_kernel_in701.md.

Finite certificate for the explicit fourteen-vertex graph.
-/

open scoped Sym2
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
open In701Deficit14

theorem in715_deficit_pack_eq : simple_graph_triangle_packing_number G = 7 := by
  unfold simple_graph_triangle_packing_number
  refine IsGreatest.csSup_eq ⟨⟨P,in715_deficit_p_tri,in715_deficit_p_disj,in715_deficit_p_size⟩,?_⟩
  rintro k ⟨Q,hQ,hpair,rfl⟩
  have h := in701_packing_le_edge_cover G C in715_deficit_c_edges in715_deficit_cover Q hQ hpair
  rw [in715_deficit_c_size] at h
  exact h
