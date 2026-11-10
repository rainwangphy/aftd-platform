import AFTD.Prelude
import AFTD.Kb.Tcs.In715DeficitPrecise
import AFTD.Kb.Tcs.In701PackingLeEdgeCover
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.In715DeficitCEdges
import AFTD.Kb.Tcs.In715DeficitCover
import AFTD.Kb.Tcs.In715DeficitPSize

/-!
# simple_graph_deficit_two_example_two_edge_drop

Topic: graphs   Node: c6cc511571bc

Provenance: helper lemma. Two-edge-deletion certificate for the finite local-count example in state/campaigns/triangle_reductions/outside_induced_kernel_in701.md.

Deleting two specified base edges from the explicit 14-vertex local-count counterexample decreases its triangle-packing number from seven to at most five.
-/

open scoped Sym2
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

noncomputable def in715_dropG : SimpleGraph (Fin 14) :=
  In701Deficit14.G.deleteEdges {s(0,1),s(0,4)}

def in715_dropC : Finset (Sym2 (Fin 14)) :=
  {s(1,2),s(2,3),s(3,4),s(0,11),s(1,11)}

theorem in715_dropC_edges : ∀ e ∈ in715_dropC, e ∈ in715_dropG.edgeSet := by
  intro e he
  simp only [in715_dropC, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  all_goals
    apply (SimpleGraph.mem_edgeSet _).mpr
    apply SimpleGraph.deleteEdges_adj.mpr
    constructor
    · decide +kernel
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor <;> decide +kernel

theorem in715_dropC_card : in715_dropC.card = 5 := by decide +kernel

theorem in715_dropC_cover : ∀ t : Finset (Fin 14), in715_dropG.IsNClique 3 t →
    ∃ e ∈ in715_dropC, e ∈ t.sym2 := by
  intro t ht
  have htG : In701Deficit14.G.IsNClique 3 t := ht.mono (SimpleGraph.deleteEdges_le _)
  obtain ⟨e, heC, het⟩ := in715_deficit_cover t htG
  have heG := in715_deficit_c_edges e heC
  obtain ⟨⟨u,v⟩, rfl⟩ := Sym2.mk_surjective e
  have huv : u ≠ v := ((SimpleGraph.mem_edgeSet _).mp heG).ne
  have huvT := Finset.mem_sym2_iff.mp het
  have hu : u ∈ t := huvT u (by simp)
  have hv : v ∈ t := huvT v (by simp)
  have hd : s(u,v) ∈ in715_dropG.edgeSet := (SimpleGraph.mem_edgeSet _).mpr (ht.isClique hu hv huv)
  have hne1 : s(u,v) ≠ s(0,1) := by
    intro h
    have ha := (SimpleGraph.deleteEdges_adj.mp ((SimpleGraph.mem_edgeSet _).mp hd)).2
    exact ha (by simp [h])
  have hne2 : s(u,v) ≠ s(0,4) := by
    intro h
    have ha := (SimpleGraph.deleteEdges_adj.mp ((SimpleGraph.mem_edgeSet _).mp hd)).2
    exact ha (by simp [h])
  refine ⟨s(u,v), ?_, het⟩
  simpa [In701Deficit14.C, in715_dropC, hne1, hne2] using heC

theorem in715_deficit_drop : simple_graph_triangle_packing_number in715_dropG ≤ 5 := by
  classical
  unfold simple_graph_triangle_packing_number
  refine csSup_le ⟨0, ∅, by simp, by simp, rfl⟩ ?_
  rintro n ⟨Q, hQ, hpair, rfl⟩
  have h := in701_packing_le_edge_cover in715_dropG in715_dropC in715_dropC_edges
    in715_dropC_cover Q hQ hpair
  simpa [in715_dropC_card] using h

theorem simple_graph_deficit_two_example_two_edge_drop : simple_graph_triangle_packing_number (In701Deficit14.G.deleteEdges {s(0,1),s(0,4)}) ≤ 5 := by exact in715_deficit_drop
