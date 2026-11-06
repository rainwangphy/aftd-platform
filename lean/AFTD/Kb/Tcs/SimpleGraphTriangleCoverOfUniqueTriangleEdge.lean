import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumberLeTwoMulPackingOfLocalCertificate
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumber

/-!
# simple_graph_triangle_cover_of_unique_triangle_edge

Topic: graphs   Node: 45d747262625

Provenance: helper lemma. Local reduction for the triangle packing campaign; motivated by the unique-triangle edges in experiment 16558.

If an edge belongs to exactly one triangle, then the triangle cover-packing inequality for the graph obtained by deleting the other two edges of that triangle implies it for the original graph.
-/

private lemma simple_graph_triangle_cover_of_unique_triangle_edge_mem_encoding_iff
    {V : Type*} [DecidableEq V] {s : Finset V} {e : Sym2 V} :
    e ∈ finite_vertex_set_edge_encoding s ↔ (∀ x ∈ e, x ∈ s) ∧ ¬ e.IsDiag := by
  unfold finite_vertex_set_edge_encoding
  rw [Finset.mem_filter, Finset.mem_sym2_iff]

private lemma simple_graph_triangle_cover_of_unique_triangle_edge_enc_of_mem_ne
    {V : Type*} [DecidableEq V] {s : Finset V} {u v : V}
    (hu : u ∈ s) (hv : v ∈ s) (huv : u ≠ v) :
    s(u, v) ∈ finite_vertex_set_edge_encoding s := by
  rw [simple_graph_triangle_cover_of_unique_triangle_edge_mem_encoding_iff]
  exact ⟨fun x hx => by rw [Sym2.mem_iff] at hx; rcases hx with rfl | rfl <;> assumption,
    by rw [Sym2.mk_isDiag_iff]; exact huv⟩

private lemma simple_graph_triangle_cover_of_unique_triangle_edge_enc_subset_edge_set
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {s : Finset V}
    (hs : G.IsNClique 3 s) : ↑(finite_vertex_set_edge_encoding s) ⊆ G.edgeSet := by
  intro e he
  simp only [Finset.mem_coe] at he
  rw [simple_graph_triangle_cover_of_unique_triangle_edge_mem_encoding_iff] at he
  obtain ⟨hsub, hdiag⟩ := he
  induction e using Sym2.ind with
  | _ u v =>
    rw [Sym2.mk_isDiag_iff] at hdiag
    rw [SimpleGraph.mem_edgeSet]
    exact hs.isClique (hsub u (by rw [Sym2.mem_iff]; left; rfl))
      (hsub v (by rw [Sym2.mem_iff]; right; rfl)) hdiag

private lemma simple_graph_triangle_cover_of_unique_triangle_edge_enc_eq_three_set
    {V : Type*} [DecidableEq V] (a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    finite_vertex_set_edge_encoding ({a, b, c} : Finset V) =
      {s(a,b), s(a,c), s(b,c)} := by
  unfold finite_vertex_set_edge_encoding
  ext e
  rw [Finset.mem_filter, Finset.mem_sym2_iff]
  induction e using Sym2.ind with
  | _ x y =>
    simp only [Sym2.mk_isDiag_iff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h, hne⟩
      have hx : x = a ∨ x = b ∨ x = c := h x (by rw [Sym2.mem_iff]; left; rfl)
      have hy : y = a ∨ y = b ∨ y = c := h y (by rw [Sym2.mem_iff]; right; rfl)
      rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl <;>
        simp_all
    · intro h
      constructor
      · intro z hz
        rw [Sym2.mem_iff] at hz
        rcases h with h|h|h <;>
          (rw [Sym2.eq_iff] at h; rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;>
          rcases hz with rfl|rfl <;> simp
      · rcases h with h|h|h <;>
          (rw [Sym2.eq_iff] at h; rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> simp_all [eq_comm]

private lemma simple_graph_triangle_cover_of_unique_triangle_edge_card_enc_eq_three
    {V : Type*} [DecidableEq V] {s : Finset V}
    (hs : s.card = 3) : (finite_vertex_set_edge_encoding s).card = 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs
  rw [simple_graph_triangle_cover_of_unique_triangle_edge_enc_eq_three_set a b c hab hac hbc]
  simp [hab, hac, hbc, hab.symm, hbc.symm]

private lemma simple_graph_triangle_cover_of_unique_triangle_edge_not_clique_of_deleted
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {t : Finset V} {e : Sym2 V}
    (ht : G.IsNClique 3 t) (_he : e ∈ finite_vertex_set_edge_encoding t) :
    ¬ (G.deleteEdges (↑(finite_vertex_set_edge_encoding t \ {e}) : Set (Sym2 V))).IsNClique 3 t := by
  intro hH
  have hcard : (finite_vertex_set_edge_encoding t).card = 3 :=
    simple_graph_triangle_cover_of_unique_triangle_edge_card_enc_eq_three ht.card_eq
  have hf : ∃ f ∈ finite_vertex_set_edge_encoding t, f ≠ e := by
    by_contra h
    push Not at h
    have h1 : (finite_vertex_set_edge_encoding t).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [h a ha, h b hb]
    omega
  obtain ⟨f, hfenc, hfe⟩ := hf
  have hfH : f ∈ (G.deleteEdges (↑(finite_vertex_set_edge_encoding t \ {e}) : Set (Sym2 V))).edgeSet :=
    simple_graph_triangle_cover_of_unique_triangle_edge_enc_subset_edge_set hH hfenc
  rw [SimpleGraph.edgeSet_deleteEdges] at hfH
  apply hfH.2
  rw [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_singleton]
  exact ⟨hfenc, hfe⟩

theorem simple_graph_triangle_cover_of_unique_triangle_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (t : Finset V) (e : Sym2 V)
    (ht : G.IsNClique 3 t) (he : e ∈ finite_vertex_set_edge_encoding t)
    (hunique : ∀ s : Finset V, G.IsNClique 3 s →
      e ∈ finite_vertex_set_edge_encoding s → s = t)
    (hind : simple_graph_triangle_cover_number
        (G.deleteEdges (↑(finite_vertex_set_edge_encoding t \ {e}) : Set (Sym2 V))) ≤
      2 * simple_graph_triangle_packing_number
        (G.deleteEdges (↑(finite_vertex_set_edge_encoding t \ {e}) : Set (Sym2 V)))) :
    simple_graph_triangle_cover_number G ≤ 2 * simple_graph_triangle_packing_number G := by
  classical
  set H := G.deleteEdges (↑(finite_vertex_set_edge_encoding t \ {e}) : Set (Sym2 V)) with hH
  set X := finite_vertex_set_edge_encoding t \ {e} with hX
  have hsub : H ≤ G := by rw [hH]; exact SimpleGraph.deleteEdges_le _
  have hind' : simple_graph_triangle_cover_number H ≤ 2 * simple_graph_triangle_packing_number H := by
    rw [hH]; exact hind
  refine simple_graph_triangle_cover_number_le_two_mul_packing_of_local_certificate
    G H hsub {t} X ?_ ?_ ?_ ?_ ?_ ?_ hind'
  · intro s hs'
    simp only [Finset.mem_singleton] at hs'
    subst s
    exact ht
  · intro s hs' t' ht' hne
    simp only [Finset.mem_coe, Finset.mem_singleton] at hs' ht'
    subst s; subst t'
    exact absurd rfl hne
  · intro s hs' t' ht'
    simp only [Finset.mem_singleton] at hs'
    subst s
    by_contra hle
    have hle' : 1 < (t ∩ t').card := by omega
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hle'
    rw [Finset.mem_inter] at hu hv
    obtain ⟨hut, hut'⟩ := hu
    obtain ⟨hvt, hvt'⟩ := hv
    have hmem_enc_t : s(u,v) ∈ finite_vertex_set_edge_encoding t :=
      simple_graph_triangle_cover_of_unique_triangle_edge_enc_of_mem_ne hut hvt huv
    have hHedge : s(u,v) ∈ H.edgeSet := by
      rw [SimpleGraph.mem_edgeSet]
      exact ht'.isClique hut' hvt' huv
    rw [hH, SimpleGraph.edgeSet_deleteEdges] at hHedge
    by_cases h_eq_e : s(u,v) = e
    · have he_enc_t' : e ∈ finite_vertex_set_edge_encoding t' := by
        rw [← h_eq_e]
        exact simple_graph_triangle_cover_of_unique_triangle_edge_enc_of_mem_ne hut' hvt' huv
      have ht'_eq : t' = t := hunique t' (ht'.mono hsub) he_enc_t'
      subst ht'_eq
      exact simple_graph_triangle_cover_of_unique_triangle_edge_not_clique_of_deleted ht he
        (by rwa [hH] at ht')
    · have hmemX : s(u,v) ∈ X := by
        rw [hX, Finset.mem_sdiff, Finset.mem_singleton]
        exact ⟨hmem_enc_t, h_eq_e⟩
      exact hHedge.2 (by simpa using hmemX)
  · intro e' he'
    rw [hX, Finset.mem_sdiff, Finset.mem_singleton] at he'
    exact simple_graph_triangle_cover_of_unique_triangle_edge_enc_subset_edge_set ht he'.1
  · intro t' ht'
    by_cases hHcl : H.IsNClique 3 t'
    · exact Or.inl hHcl
    · right
      have hnot : ¬ ∀ u ∈ t', ∀ v ∈ t', u ≠ v → H.Adj u v := by
        intro h
        exact hHcl ⟨fun u hu v hv huv => h u hu v hv huv, ht'.card_eq⟩
      push Not at hnot
      obtain ⟨u, hu, v, hv, huv, hnadj⟩ := hnot
      refine ⟨s(u,v), ?_, ?_⟩
      · have hGadj : G.Adj u v := ht'.isClique hu hv huv
        have hmem : s(u,v) ∈ (↑X : Set (Sym2 V)) := by
          by_contra hnotmem
          apply hnadj
          rw [hH, SimpleGraph.deleteEdges_adj]
          exact ⟨hGadj, hnotmem⟩
        simpa using hmem
      · intro x hx
        rw [Sym2.mem_iff] at hx
        rcases hx with rfl | rfl <;> assumption
  · have hcardX : X.card = 2 := by
      rw [hX, Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem he,
        simple_graph_triangle_cover_of_unique_triangle_edge_card_enc_eq_three ht.card_eq]
    have hcardS : ({t} : Finset (Finset V)).card = 1 := by simp
    omega
