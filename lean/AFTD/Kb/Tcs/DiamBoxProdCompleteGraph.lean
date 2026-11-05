import AFTD.Prelude

/-!
# diam_boxProd_completeGraph

Topic: graphs   Node: 88fa86c00b23

Provenance: helper lemma. arXiv:2611.03956 Lemma 2.8

For every finite connected graph G on a nonempty vertex set and every integer t ≥ 2, the diameter of the Cartesian product G □ K_t is diam(G) + 1.
-/

lemma diam_boxProd_completeGraph_ediam_boxProd {α β : Type*} [Nonempty α] [Nonempty β]
    (G : SimpleGraph α) (H : SimpleGraph β) :
    (G □ H).ediam = G.ediam + H.ediam := by
  simp_rw [SimpleGraph.ediam_eq_iSup_iSup_edist, SimpleGraph.edist_boxProd, iSup_prod]
  rw [ENat.iSup_add]
  simp_rw [ENat.iSup_add, ENat.add_iSup]
  congr 1; ext a₁
  rw [iSup_comm]

/-- The diameter of the Cartesian product of a connected graph with K_t (t ≥ 2) is diam(G) + 1. -/
theorem diam_boxProd_completeGraph {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hG : G.Connected) (t : ℕ) (ht : 2 ≤ t) :
    (G □ SimpleGraph.completeGraph (Fin t)).diam = G.diam + 1 := by
  have h_nontriv : Nontrivial (Fin t) := Fin.nontrivial_iff_two_le.mpr ht
  have h_nonempty : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp (by omega)
  have h_ediam_top : (SimpleGraph.completeGraph (Fin t)).ediam = 1 := by
    change (⊤ : SimpleGraph (Fin t)).ediam = 1
    exact SimpleGraph.ediam_top
  have hG_ne_top : G.ediam ≠ ⊤ := G.connected_iff_ediam_ne_top.mp hG
  have hH_ne_top : (SimpleGraph.completeGraph (Fin t)).ediam ≠ ⊤ := by
    rw [h_ediam_top]
    decide
  unfold SimpleGraph.diam
  rw [diam_boxProd_completeGraph_ediam_boxProd]
  rw [ENat.toNat_add hG_ne_top hH_ne_top]
  rw [h_ediam_top]
  rfl
