import AFTD.Prelude
import AFTD.Kb.Tcs.In715DeficitPSize
import AFTD.Kb.Tcs.In715DeficitLinkIsCycle
import AFTD.Kb.Tcs.In715DeficitCEdges
import AFTD.Kb.Tcs.In715DeficitCSize
import AFTD.Kb.Tcs.In715DeficitCover
import AFTD.Kb.Tcs.In715DeficitPTri
import AFTD.Kb.Tcs.In715DeficitPDisj
import AFTD.Kb.Tcs.In715DeficitPackEq
import AFTD.Kb.Tcs.In715DeficitOutside
import AFTD.Kb.Tcs.In715DeficitMissing
import AFTD.Kb.Tcs.In715DeficitPrivateTip
import AFTD.Kb.Tcs.In715DeficitXlink
import AFTD.Kb.Tcs.In715DeficitZOk
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# in715_deficit_precise

Topic: graphs   Node: 1abbea12ae00

Provenance: helper lemma. Finite graph and certificates from experiments 20940 and 20968; see state/campaigns/triangle_reductions/outside_induced_kernel_in701.md.

An explicit fourteen-vertex graph has a maximum seven-triangle packing, a seven-edge triangle cover, an outside five-cycle link and a private packed tip missing a link vertex despite belonging to at least five triangles.
-/

open scoped Sym2
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem in715_deficit_precise :
    (∀ e ∈ In701Deficit14.C, e ∈ In701Deficit14.G.edgeSet) ∧
    In701Deficit14.C.card = 7 ∧
    (∀ t : Finset (Fin 14), In701Deficit14.G.IsNClique 3 t →
      ∃ e ∈ In701Deficit14.C, e ∈ t.sym2) ∧
    (∀ t ∈ In701Deficit14.P, In701Deficit14.G.IsNClique 3 t) ∧
    (In701Deficit14.P : Set (Finset (Fin 14))).Pairwise (fun a b => (a ∩ b).card ≤ 1) ∧
    In701Deficit14.P.card = 7 ∧ simple_graph_triangle_packing_number In701Deficit14.G = 7 ∧
    (10 : Fin 14) ∉ In701Deficit14.P.biUnion id ∧ ¬ In701Deficit14.G.Adj 9 3 ∧
    ({0,4,9} : Finset (Fin 14)) ∈ In701Deficit14.P ∧
    (∀ t ∈ In701Deficit14.P, (9 : Fin 14) ∈ t → t = ({0,4,9} : Finset (Fin 14))) ∧
    (∀ v : Fin 14, In701Deficit14.G.Adj 10 v ↔ v ∈ ({0,1,2,3,4} : Finset (Fin 14))) ∧
    (∀ u v : Fin 14, u ∈ ({0,1,2,3,4} : Finset (Fin 14)) →
      v ∈ ({0,1,2,3,4} : Finset (Fin 14)) →
      (In701Deficit14.G.Adj u v ↔ s(u,v) ∈
        ({s(0,1),s(1,2),s(2,3),s(3,4),s(0,4)} : Finset (Sym2 (Fin 14))))) ∧
    In701Deficit14.Z.card = 5 ∧
    (∀ t ∈ In701Deficit14.Z, In701Deficit14.G.IsNClique 3 t ∧ (9 : Fin 14) ∈ t) := by
  exact ⟨in715_deficit_c_edges, in715_deficit_c_size, in715_deficit_cover,
    in715_deficit_p_tri, in715_deficit_p_disj, in715_deficit_p_size,
    in715_deficit_pack_eq, in715_deficit_outside, in715_deficit_missing,
    in715_deficit_private_tip.1, in715_deficit_private_tip.2,
    in715_deficit_xlink, in715_deficit_link_is_cycle,
    in715_deficit_z_ok.1, in715_deficit_z_ok.2⟩
