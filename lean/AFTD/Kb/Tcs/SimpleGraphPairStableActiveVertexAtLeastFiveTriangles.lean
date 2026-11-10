import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphPairStableVertexLinkEdgeSpokeExchange
import AFTD.Kb.Tcs.SimpleGraphPairStableVertexLinkNotFourCycle
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# simple_graph_pair_stable_active_vertex_at_least_five_triangles

Topic: graphs   Node: 2097b39f74bb

Provenance: helper lemma. Two-edge-stable triangle-packing residual; exhaustive link audit experiment 20286. No novelty claim.

In a finite graph whose maximum triangle-packing number survives every two-edge deletion, any vertex that lies in a triangle lies in at least five distinct triangles.
-/

open scoped Sym2

private lemma simple_graph_pair_stable_active_vertex_at_least_five_triangles_link_mem_iff
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x a b : Fin n) :
    s(a,b) ∈ G.edgeFinset.filter (fun e => ∀ v ∈ e, G.Adj x v) ↔
      G.Adj a b ∧ G.Adj x a ∧ G.Adj x b := by
  simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset]
  rw [SimpleGraph.mem_edgeSet, Sym2.ball]

private lemma simple_graph_pair_stable_active_vertex_at_least_five_triangles_exchange_mem
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n)
    (hstable : ∀ e f : Sym2 (Fin n), e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f →
      simple_graph_triangle_packing_number (G.deleteEdges {e,f}) =
        simple_graph_triangle_packing_number G)
    (y z w : Fin n) (hy : G.Adj x y) (hz : G.Adj x z) (hyz : G.Adj y z) (hw : G.Adj x w) :
    ∃ u v, s(u,v) ∈ G.edgeFinset.filter (fun e => ∀ v ∈ e, G.Adj x v) ∧
      (u = y ∨ u = z ∨ v = y ∨ v = z) ∧ u ≠ w ∧ v ≠ w ∧ s(u,v) ≠ s(y,z) := by
  obtain ⟨u, v, hxu, hxv, huv, hmem, huw, hvw, hne⟩ :=
    simple_graph_pair_stable_vertex_link_edge_spoke_exchange n G x hstable y z w hy hz hyz hw
  refine ⟨u, v, ?_, hmem, huw, hvw, hne⟩
  rw [simple_graph_pair_stable_active_vertex_at_least_five_triangles_link_mem_iff]
  exact ⟨huv, hxu, hxv⟩

private lemma simple_graph_pair_stable_active_vertex_at_least_five_triangles_other_edge_left
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n)
    (hstable : ∀ e f : Sym2 (Fin n), e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f →
      simple_graph_triangle_packing_number (G.deleteEdges {e,f}) =
        simple_graph_triangle_packing_number G)
    (y z : Fin n) (hy : G.Adj x y) (hz : G.Adj x z) (hyz : G.Adj y z) :
    ∃ a, G.Adj y a ∧ G.Adj x a ∧ a ≠ z ∧
      s(y,a) ∈ G.edgeFinset.filter (fun e => ∀ v ∈ e, G.Adj x v) := by
  obtain ⟨u, v, hmemE, hex, huz, hvz, hne⟩ :=
    simple_graph_pair_stable_active_vertex_at_least_five_triangles_exchange_mem
      n G x hstable y z z hy hz hyz hz
  rw [simple_graph_pair_stable_active_vertex_at_least_five_triangles_link_mem_iff] at hmemE
  obtain ⟨huv, hxu, hxv⟩ := hmemE
  rcases hex with huy | huz' | hvy | hvz'
  · refine ⟨v, by simpa [huy] using huv, hxv, hvz, ?_⟩
    rw [show s(y,v) = s(u,v) by rw [huy],
      simple_graph_pair_stable_active_vertex_at_least_five_triangles_link_mem_iff]
    exact ⟨huv, hxu, hxv⟩
  · exact absurd huz' huz
  · refine ⟨u, by simpa [hvy] using huv.symm, hxu, huz, ?_⟩
    rw [show s(y,u) = s(u,v) by rw [hvy, Sym2.eq_swap],
      simple_graph_pair_stable_active_vertex_at_least_five_triangles_link_mem_iff]
    exact ⟨huv, hxu, hxv⟩
  · exact absurd hvz' hvz

private lemma simple_graph_pair_stable_active_vertex_at_least_five_triangles_other_edge_right
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n)
    (hstable : ∀ e f : Sym2 (Fin n), e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f →
      simple_graph_triangle_packing_number (G.deleteEdges {e,f}) =
        simple_graph_triangle_packing_number G)
    (y z : Fin n) (hy : G.Adj x y) (hz : G.Adj x z) (hyz : G.Adj y z) :
    ∃ b, G.Adj z b ∧ G.Adj x b ∧ b ≠ y ∧
      s(z,b) ∈ G.edgeFinset.filter (fun e => ∀ v ∈ e, G.Adj x v) := by
  obtain ⟨u, v, hmemE, hex, huy, hvy, hne⟩ :=
    simple_graph_pair_stable_active_vertex_at_least_five_triangles_exchange_mem
      n G x hstable y z y hy hz hyz hy
  rw [simple_graph_pair_stable_active_vertex_at_least_five_triangles_link_mem_iff] at hmemE
  obtain ⟨huv, hxu, hxv⟩ := hmemE
  rcases hex with huz | huz' | hvz | hvz'
  · exact absurd huz huy
  · refine ⟨v, by simpa [huz'] using huv, hxv, hvy, ?_⟩
    rw [show s(z,v) = s(u,v) by rw [huz'],
      simple_graph_pair_stable_active_vertex_at_least_five_triangles_link_mem_iff]
    exact ⟨huv, hxu, hxv⟩
  · exact absurd hvz hvy
  · refine ⟨u, by simpa [hvz'] using huv.symm, hxu, huy, ?_⟩
    rw [show s(z,u) = s(u,v) by rw [hvz', Sym2.eq_swap],
      simple_graph_pair_stable_active_vertex_at_least_five_triangles_link_mem_iff]
    exact ⟨huv, hxu, hxv⟩

private lemma simple_graph_pair_stable_active_vertex_at_least_five_triangles_active_link_edge
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n)
    (hactive : ∃ t : Finset (Fin n), G.IsNClique 3 t ∧ x ∈ t) :
    ∃ y z, G.Adj x y ∧ G.Adj x z ∧ G.Adj y z ∧
      s(y,z) ∈ G.edgeFinset.filter (fun e => ∀ v ∈ e, G.Adj x v) := by
  obtain ⟨t, ht, hxt⟩ := hactive
  rw [SimpleGraph.is3Clique_iff] at ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxt
  rcases hxt with rfl | rfl | rfl
  · exact ⟨b, c, hab, hac, hbc, by
      rw [simple_graph_pair_stable_active_vertex_at_least_five_triangles_link_mem_iff]
      exact ⟨hbc, hab, hac⟩⟩
  · exact ⟨a, c, hab.symm, hbc, hac, by
      rw [simple_graph_pair_stable_active_vertex_at_least_five_triangles_link_mem_iff]
      exact ⟨hac, hab.symm, hbc⟩⟩
  · exact ⟨a, b, hac.symm, hbc.symm, hab, by
      rw [simple_graph_pair_stable_active_vertex_at_least_five_triangles_link_mem_iff]
      exact ⟨hab, hac.symm, hbc.symm⟩⟩

private lemma simple_graph_pair_stable_active_vertex_at_least_five_triangles_five_of_four
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n)
    (T : Finset (Sym2 (Fin n))) (g : Sym2 (Fin n)) (hT4 : T.card = 4)
    (hTsub : T ⊆ G.edgeFinset.filter (fun e => ∀ v ∈ e, G.Adj x v))
    (hgE : g ∈ G.edgeFinset.filter (fun e => ∀ v ∈ e, G.Adj x v)) (hgT : g ∉ T) :
    5 ≤ (G.edgeFinset.filter (fun e => ∀ v ∈ e, G.Adj x v)).card := by
  have hcard : (insert g T).card = 5 := by
    rw [Finset.card_insert_of_notMem hgT, hT4]
  have hsub : insert g T ⊆ G.edgeFinset.filter (fun e => ∀ v ∈ e, G.Adj x v) := by
    intro e he
    rw [Finset.mem_insert] at he
    rcases he with rfl | h
    · exact hgE
    · exact hTsub h
  calc 5 = (insert g T).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

private lemma simple_graph_pair_stable_active_vertex_at_least_five_triangles_triangle_extra_five
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n)
    (hstable : ∀ e f : Sym2 (Fin n), e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f →
      simple_graph_triangle_packing_number (G.deleteEdges {e,f}) =
        simple_graph_triangle_packing_number G)
    (y z p : Fin n) (hy : G.Adj x y) (hz : G.Adj x z) (hp : G.Adj x p)
    (hyz : G.Adj y z) (hyp : G.Adj y p) (hzp : G.Adj z p)
    (g : Sym2 (Fin n))
    (hgE : g ∈ G.edgeFinset.filter (fun e => ∀ v ∈ e, G.Adj x v))
    (hgT : g ∉ ({s(y,z), s(y,p), s(z,p)} : Finset (Sym2 (Fin n)))) :
    5 ≤ (G.edgeFinset.filter (fun e => ∀ v ∈ e, G.Adj x v)).card := by
  have hyp' : y ≠ p := hyp.ne
  have hzp' : z ≠ p := hzp.ne
  have hyz' : y ≠ z := hyz.ne
  have hgnd : ¬ g.IsDiag := G.not_isDiag_of_mem_edgeFinset (Finset.mem_filter.mp hgE).1
  obtain ⟨r, s, hg_eq⟩ : ∃ r s, g = s(r,s) := by
    induction g using Sym2.ind with
    | _ r s => exact ⟨r, s, rfl⟩
  subst hg_eq
  rw [simple_graph_pair_stable_active_vertex_at_least_five_triangles_link_mem_iff] at hgE
  obtain ⟨hrs, hxr, hxs⟩ := hgE
  have hrne : r ≠ s := hrs.ne
  have hout : r ∉ ({y,z,p} : Finset (Fin n)) ∨ s ∉ ({y,z,p} : Finset (Fin n)) := by
    by_contra h
    push Not at h
    obtain ⟨hr, hs⟩ := h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr hs hgT
    rcases hr with rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hrne
      | exact hgT (by simp)
  obtain ⟨u, v, hg_eq2, huv, hxu, hxv, huout, huv_ne⟩ :
      ∃ u v, s(u,v) = s(r,s) ∧ G.Adj u v ∧ G.Adj x u ∧ G.Adj x v ∧
        u ∉ ({y,z,p} : Finset (Fin n)) ∧ u ≠ v := by
    rcases hout with hr | hs
    · exact ⟨r, s, rfl, hrs, hxr, hxs, hr, hrne⟩
    · exact ⟨s, r, by rw [Sym2.eq_swap], hrs.symm, hxs, hxr, hs, hrne.symm⟩
  obtain ⟨u2, huu2, hxu2, hu2v, hu2E⟩ :=
    simple_graph_pair_stable_active_vertex_at_least_five_triangles_other_edge_left
      n G x hstable u v hxu hxv huv
  set T : Finset (Sym2 (Fin n)) := {s(y,z), s(y,p), s(z,p)} with hTdef
  have hTsub : T ⊆ G.edgeFinset.filter (fun e => ∀ v ∈ e, G.Adj x v) := by
    intro e he
    simp only [hTdef, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · rw [simple_graph_pair_stable_active_vertex_at_least_five_triangles_link_mem_iff]
      exact ⟨hyz, hy, hz⟩
    · rw [simple_graph_pair_stable_active_vertex_at_least_five_triangles_link_mem_iff]
      exact ⟨hyp, hy, hp⟩
    · rw [simple_graph_pair_stable_active_vertex_at_least_five_triangles_link_mem_iff]
      exact ⟨hzp, hz, hp⟩
  have hTcard : T.card = 3 := by
    rw [hTdef]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    all_goals simp [hyp', hzp', hyz']
  have hg'ne : s(u,u2) ∉ T := by
    intro hmem
    simp only [hTdef, Finset.mem_insert, Finset.mem_singleton] at hmem
    have hu : u ∈ s(u,u2) := Sym2.mem_mk_left u u2
    rcases hmem with hmem | hmem | hmem
    all_goals
      rw [hmem] at hu
      simp only [Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton] at hu
      exact huout (by rcases hu with h|h <;> simp [h])
  have hgg' : s(u,u2) ≠ s(u,v) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hu2v h2
    · exact huv_ne h1
  have hgT' : s(u,v) ∉ T := by
    rw [hg_eq2]; exact hgT
  have hgin : s(u,v) ∉ insert s(u,u2) T := by
    intro h
    rw [Finset.mem_insert] at h
    rcases h with h | h
    · exact hgg' h.symm
    · exact hgT' h
  have hcard5 : (insert s(u,v) (insert s(u,u2) T)).card = 5 := by
    rw [Finset.card_insert_of_notMem hgin, Finset.card_insert_of_notMem hg'ne, hTcard]
  have hsub : insert s(u,v) (insert s(u,u2) T) ⊆
      G.edgeFinset.filter (fun e => ∀ v ∈ e, G.Adj x v) := by
    intro e he
    rw [Finset.mem_insert, Finset.mem_insert] at he
    rcases he with rfl | rfl | hT
    · rw [simple_graph_pair_stable_active_vertex_at_least_five_triangles_link_mem_iff]
      exact ⟨huv, hxu, hxv⟩
    · rw [simple_graph_pair_stable_active_vertex_at_least_five_triangles_link_mem_iff]
      exact ⟨huu2, hxu, hxu2⟩
    · exact hTsub hT
  calc 5 = (insert s(u,v) (insert s(u,u2) T)).card := hcard5.symm
    _ ≤ _ := Finset.card_le_card hsub

private lemma simple_graph_pair_stable_active_vertex_at_least_five_triangles_link_card_ge_five
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n)
    (hstable : ∀ e f : Sym2 (Fin n), e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f →
      simple_graph_triangle_packing_number (G.deleteEdges {e,f}) =
        simple_graph_triangle_packing_number G)
    (hactive : ∃ t : Finset (Fin n), G.IsNClique 3 t ∧ x ∈ t) :
    5 ≤ (G.edgeFinset.filter (fun e => ∀ v ∈ e, G.Adj x v)).card := by
  let E : Finset (Sym2 (Fin n)) := G.edgeFinset.filter (fun e => ∀ v ∈ e, G.Adj x v)
  change 5 ≤ E.card
  by_contra hgoal
  have hle : E.card ≤ 4 := by omega
  obtain ⟨y, z, hy, hz, hyz, hyzE⟩ :=
    simple_graph_pair_stable_active_vertex_at_least_five_triangles_active_link_edge n G x hactive
  obtain ⟨p, hyp, hxp, hpz, hypE⟩ :=
    simple_graph_pair_stable_active_vertex_at_least_five_triangles_other_edge_left
      n G x hstable y z hy hz hyz
  obtain ⟨q, hzq, hxq, hqy, hzqE⟩ :=
    simple_graph_pair_stable_active_vertex_at_least_five_triangles_other_edge_right
      n G x hstable y z hy hz hyz
  have hpy : p ≠ y := hyp.ne.symm
  have hqz : q ≠ z := hzq.ne.symm
  have hyq : y ≠ q := hqy.symm
  have hyz_ne : y ≠ z := hyz.ne
  have hzp : z ≠ p := hpz.symm
  by_cases hpq : p = q
  · subst q
    set T : Finset (Sym2 (Fin n)) := {s(y,z), s(y,p), s(z,p)} with hTdef
    have hTsub : T ⊆ E := by
      intro e he
      simp only [hTdef, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl
      · exact hyzE
      · exact hypE
      · exact hzqE
    by_cases hsub : E ⊆ T
    · have hET : E = T := Finset.Subset.antisymm hsub hTsub
      obtain ⟨u, v, huve, hdisj, hup, hvp, hne⟩ :=
        simple_graph_pair_stable_active_vertex_at_least_five_triangles_exchange_mem
          n G x hstable y z p hy hz hyz hxp
      have huve' : s(u,v) ∈ E := huve
      rw [hET] at huve'
      simp only [hTdef, Finset.mem_insert, Finset.mem_singleton] at huve'
      rcases huve' with h | h | h
      · exact hne h
      · have hpmem : p ∈ s(u,v) := by rw [h]; exact Sym2.mem_mk_right y p
        simp only [Sym2.mem_iff] at hpmem
        rcases hpmem with h' | h'
        · exact hup h'.symm
        · exact hvp h'.symm
      · have hpmem : p ∈ s(u,v) := by rw [h]; exact Sym2.mem_mk_right z p
        simp only [Sym2.mem_iff] at hpmem
        rcases hpmem with h' | h'
        · exact hup h'.symm
        · exact hvp h'.symm
    · obtain ⟨g, hgE, hgT⟩ := Finset.not_subset.mp hsub
      have h5 : 5 ≤ E.card :=
        simple_graph_pair_stable_active_vertex_at_least_five_triangles_triangle_extra_five
          n G x hstable y z p hy hz hxp hyz hyp hzq g hgE hgT
      omega
  · have hpq' : p ≠ q := hpq
    obtain ⟨r, hpr, hxr, hry, hprE⟩ :=
      simple_graph_pair_stable_active_vertex_at_least_five_triangles_other_edge_left
        n G x hstable p y hxp hy hyp.symm
    by_cases hrq : r = q
    · subst r
      set T4 : Finset (Sym2 (Fin n)) := {s(y,z), s(z,q), s(q,p), s(p,y)} with hT4def
      have hT4sub : T4 ⊆ E := by
        intro e he
        simp only [hT4def, Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl | rfl
        · exact hyzE
        · exact hzqE
        · rw [Sym2.eq_swap]; exact hprE
        · rw [Sym2.eq_swap]; exact hypE
      have hT4card : T4.card = 4 := by
        rw [hT4def]
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_singleton]
        all_goals simp [Sym2.eq_iff, hyz_ne, hqz, hpq', hpy, hyq, hzp,
          hyz_ne.symm, hqz.symm, hpq'.symm, hpy.symm, hyq.symm, hzp.symm]
      have hET4 : E = T4 := (Finset.eq_of_subset_of_card_le hT4sub (by omega)).symm
      have hcard4 : ({y,z,q,p} : Finset (Fin n)).card = 4 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_singleton]
        all_goals simp [hyz_ne, hyq, hyp.ne, hqz, hzp, hpq', hyz_ne.symm, hyq.symm,
          hyp.ne.symm, hqz.symm, hzp.symm, hpq'.symm]
      have hneq := simple_graph_pair_stable_vertex_link_not_four_cycle n G x hstable y z q p hcard4
      apply hneq
      simpa only [hT4def] using hET4
    · have hrq' : r ≠ q := hrq
      set T4 : Finset (Sym2 (Fin n)) := {s(y,z), s(y,p), s(z,q), s(p,r)} with hT4def
      have hT4sub : T4 ⊆ E := by
        intro e he
        simp only [hT4def, Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl | rfl
        · exact hyzE
        · exact hypE
        · exact hzqE
        · exact hprE
      have hT4card : T4.card = 4 := by
        rw [hT4def]
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_singleton]
        all_goals simp [Sym2.eq_iff, hyz_ne, hyp.ne, hqz, hry, hpq', hpz, hyq,
          hyz_ne.symm, hyp.ne.symm, hqz.symm, hry.symm, hpq'.symm, hpz.symm, hyq.symm]
      obtain ⟨b, hqb, hxb, hbz, hqbE⟩ :=
        simple_graph_pair_stable_active_vertex_at_least_five_triangles_other_edge_left
          n G x hstable q z hxq hz hzq.symm
      have hgqT : s(q,b) ∉ T4 := by
        intro hmem
        simp only [hT4def, Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h | h | h | h
        · have hqm : q ∈ s(y,z) := by rw [← h]; exact Sym2.mem_mk_left q b
          simp only [Sym2.mem_iff] at hqm
          rcases hqm with h' | h'
          · exact hqy h'
          · exact hqz h'
        · have hqm : q ∈ s(y,p) := by rw [← h]; exact Sym2.mem_mk_left q b
          simp only [Sym2.mem_iff] at hqm
          rcases hqm with h' | h'
          · exact hqy h'
          · exact hpq' h'.symm
        · have hbm : b ∈ s(z,q) := by rw [← h]; exact Sym2.mem_mk_right q b
          simp only [Sym2.mem_iff] at hbm
          rcases hbm with h' | h'
          · exact hbz h'
          · exact hqb.ne.symm h'
        · have hqm : q ∈ s(p,r) := by rw [← h]; exact Sym2.mem_mk_left q b
          simp only [Sym2.mem_iff] at hqm
          rcases hqm with h' | h'
          · exact hpq' h'.symm
          · exact hrq' h'.symm
      have h5 : 5 ≤ E.card :=
        simple_graph_pair_stable_active_vertex_at_least_five_triangles_five_of_four
          n G x T4 (s(q,b)) hT4card hT4sub hqbE hgqT
      omega

private lemma simple_graph_pair_stable_active_vertex_at_least_five_triangles_edge_card_le_triangle_card
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n) :
    (G.edgeFinset.filter (fun e => ∀ v ∈ e, G.Adj x v)).card ≤
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun t => G.IsNClique 3 t ∧ x ∈ t)).card := by
  let E : Finset (Sym2 (Fin n)) := G.edgeFinset.filter (fun e => ∀ v ∈ e, G.Adj x v)
  let T : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Finset (Fin n))).filter (fun t => G.IsNClique 3 t ∧ x ∈ t)
  change E.card ≤ T.card
  apply Finset.card_le_card_of_injOn (fun e : Sym2 (Fin n) => insert x e.toFinset)
  · intro e he
    have heE : e ∈ G.edgeFinset.filter (fun e => ∀ v ∈ e, G.Adj x v) := he
    obtain ⟨r, s, heq⟩ : ∃ r s, e = s(r,s) := by
      induction e using Sym2.ind with
      | _ r s => exact ⟨r, s, rfl⟩
    subst heq
    obtain ⟨hrs, hxr, hxs⟩ :=
      (simple_graph_pair_stable_active_vertex_at_least_five_triangles_link_mem_iff n G x r s).mp heE
    change insert x (s(r,s)).toFinset ∈ T
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · have hxf : insert x (s(r,s)).toFinset = {x, r, s} := by
        rw [Sym2.toFinset_mk_eq]
      rw [hxf, SimpleGraph.is3Clique_triple_iff]
      exact ⟨hxr, hxs, hrs⟩
    · exact Finset.mem_insert_self x _
  · intro e1 he1 e2 he2 h
    have he1E : e1 ∈ G.edgeFinset.filter (fun e => ∀ v ∈ e, G.Adj x v) := he1
    have he2E : e2 ∈ G.edgeFinset.filter (fun e => ∀ v ∈ e, G.Adj x v) := he2
    have hx1 : x ∉ e1.toFinset := by
      intro hx
      have hx' : x ∈ e1 := Sym2.mem_toFinset.mp hx
      exact ((Finset.mem_filter.mp he1E).2 x hx').ne rfl
    have hx2 : x ∉ e2.toFinset := by
      intro hx
      have hx' : x ∈ e2 := Sym2.mem_toFinset.mp hx
      exact ((Finset.mem_filter.mp he2E).2 x hx').ne rfl
    have hto : e1.toFinset = e2.toFinset := by
      have hcongr := congrArg (fun t : Finset (Fin n) => t.erase x) h
      rw [Finset.erase_insert hx1, Finset.erase_insert hx2] at hcongr
      exact hcongr
    exact Sym2.ext (fun y => by
      rw [← Sym2.mem_toFinset, hto, Sym2.mem_toFinset])

theorem simple_graph_pair_stable_active_vertex_at_least_five_triangles (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n) (hstable : ∀ e f : Sym2 (Fin n), e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f → simple_graph_triangle_packing_number (G.deleteEdges {e,f}) = simple_graph_triangle_packing_number G) (hactive : ∃ t : Finset (Fin n), G.IsNClique 3 t ∧ x ∈ t) : 5 ≤ (((Finset.univ : Finset (Finset (Fin n))).filter (fun t => G.IsNClique 3 t ∧ x ∈ t)).card) := by
  have hE5 : 5 ≤ (G.edgeFinset.filter (fun e => ∀ v ∈ e, G.Adj x v)).card :=
    simple_graph_pair_stable_active_vertex_at_least_five_triangles_link_card_ge_five
      n G x hstable hactive
  have hle :=
    simple_graph_pair_stable_active_vertex_at_least_five_triangles_edge_card_le_triangle_card
      n G x
  omega
