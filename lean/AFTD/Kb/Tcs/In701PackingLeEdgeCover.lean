import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# in701_packing_le_edge_cover

Topic: graphs   Node: ceec84a39636

Provenance: helper lemma. Finite graph and certificates from experiments 20940 and 20968; see state/campaigns/triangle_reductions/outside_induced_kernel_in701.md.

A triangle packing has at most as many triangles as an edge cover.
-/

open scoped Sym2
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem in701_packing_le_edge_cover (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj]
    (C : Finset (Sym2 (Fin 14))) (hC : ∀ e ∈ C, e ∈ G.edgeSet)
    (hcover : ∀ t : Finset (Fin 14), G.IsNClique 3 t → ∃ e ∈ C, e ∈ t.sym2)
    (Q : Finset (Finset (Fin 14))) (hQ : ∀ t ∈ Q, G.IsNClique 3 t)
    (hpair : (Q : Set (Finset (Fin 14))).Pairwise (fun s t => (s ∩ t).card ≤ 1)) : Q.card ≤ C.card := by
  classical
  let f (t : Finset (Fin 14)) : Sym2 (Fin 14) :=
    if h : G.IsNClique 3 t then Classical.choose (hcover t h) else s(0,0)
  have hchosen : ∀ t ∈ Q, f t ∈ C ∧ f t ∈ t.sym2 := by
    intro t ht
    simpa only [f, dif_pos (hQ t ht)] using Classical.choose_spec (hcover t (hQ t ht))
  apply Finset.card_le_card_of_injOn f
  · intro t ht
    exact (hchosen t (Finset.mem_coe.mp ht)).1
  · intro s hs t ht heq
    by_contra hne
    have hsQ := Finset.mem_coe.mp hs
    have htQ := Finset.mem_coe.mp ht
    have hsedge := (hchosen s hsQ).2
    have htedge := (hchosen t htQ).2
    rw [← heq] at htedge
    obtain ⟨⟨u,v⟩,huv⟩ := Sym2.mk_surjective (f s)
    have huv' : s(u,v) = f s := huv
    rw [← huv'] at hsedge htedge
    have huvs : ∀ z ∈ s(u,v), z ∈ s := Finset.mem_sym2_iff.mp hsedge
    have huvt : ∀ z ∈ s(u,v), z ∈ t := Finset.mem_sym2_iff.mp htedge
    have hadj : G.Adj u v := (SimpleGraph.mem_edgeSet G).mp (by
      rw [huv']
      exact hC _ (hchosen s hsQ).1)
    have huv_ne : u ≠ v := hadj.ne
    have hi : 1 < (s ∩ t).card := Finset.one_lt_card.mpr ⟨u,by simp [huvs u (by simp), huvt u (by simp)],v,by simp [huvs v (by simp),huvt v (by simp)],huv_ne⟩
    have hl := hpair hs ht hne
    omega
