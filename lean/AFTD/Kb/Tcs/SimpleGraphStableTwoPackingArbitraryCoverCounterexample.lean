import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding

/-!
# simple_graph_stable_two_packing_arbitrary_cover_counterexample

Topic: graphs   Node: 7073e6201ccc

Provenance: helper lemma. Explicit six-vertex wheel, experiment 16018; triangle packing and covering definitions from arXiv:2610.15539, Section 1.

There is a finite edge-deletion-stable graph with triangle packing number two, a maximum packing P, and a four-edge triangle cover C such that C is not contained in the union of the edges of P and any second maximum packing.
-/

open Sym2

def simple_graph_stable_two_packing_arbitrary_cover_counterexample_edges : Finset (Sym2 (Fin 6)) :=
  {s(0,1), s(1,2), s(2,3), s(3,4), s(0,4), s(0,5), s(1,5), s(2,5), s(3,5), s(4,5)}

abbrev simple_graph_stable_two_packing_arbitrary_cover_counterexample_wheel : SimpleGraph (Fin 6) where
  Adj a b := s(a,b) ∈ simple_graph_stable_two_packing_arbitrary_cover_counterexample_edges ∧ a ≠ b
  symm := ⟨fun a b h => ⟨by simpa [Sym2.eq_swap] using h.1, h.2.symm⟩⟩
  loopless := ⟨fun a => by simp⟩

def simple_graph_stable_two_packing_arbitrary_cover_counterexample_coverSet : Finset (Sym2 (Fin 6)) :=
  {s(0,4), s(3,4), s(1,5), s(2,5)}

lemma simple_graph_stable_two_packing_arbitrary_cover_counterexample_set_pairwise_iff
    (T : Finset (Finset (Fin 6))) :
    (T : Set (Finset (Fin 6))).Pairwise (fun a b => (a ∩ b).card ≤ 1) ↔
    ∀ x ∈ T, ∀ y ∈ T, x ≠ y → (x ∩ y).card ≤ 1 := Iff.rfl

lemma simple_graph_stable_two_packing_arbitrary_cover_counterexample_three_clique_contains_five
    (t : Finset (Fin 6))
    (ht : simple_graph_stable_two_packing_arbitrary_cover_counterexample_wheel.IsNClique 3 t) :
    (5 : Fin 6) ∈ t := by
  rw [SimpleGraph.is3Clique_iff] at ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht
  exact (by decide : ∀ a b c : Fin 6,
    simple_graph_stable_two_packing_arbitrary_cover_counterexample_wheel.Adj a b →
    simple_graph_stable_two_packing_arbitrary_cover_counterexample_wheel.Adj a c →
    simple_graph_stable_two_packing_arbitrary_cover_counterexample_wheel.Adj b c →
    (5 : Fin 6) ∈ ({a, b, c} : Finset (Fin 6))) a b c hab hac hbc

lemma simple_graph_stable_two_packing_arbitrary_cover_counterexample_isNClique_mono
    {G H : SimpleGraph (Fin 6)} (h : G ≤ H) {n : ℕ} {s : Finset (Fin 6)}
    (hs : G.IsNClique n s) : H.IsNClique n s :=
  ⟨SimpleGraph.IsClique.mono h hs.1, hs.2⟩

lemma simple_graph_stable_two_packing_arbitrary_cover_counterexample_contains_five_of_le
    {H : SimpleGraph (Fin 6)}
    (h : H ≤ simple_graph_stable_two_packing_arbitrary_cover_counterexample_wheel)
    (t : Finset (Fin 6)) (ht : H.IsNClique 3 t) : (5 : Fin 6) ∈ t :=
  simple_graph_stable_two_packing_arbitrary_cover_counterexample_three_clique_contains_five t
    (simple_graph_stable_two_packing_arbitrary_cover_counterexample_isNClique_mono h ht)

lemma simple_graph_stable_two_packing_arbitrary_cover_counterexample_card_le_two_of_packing
    (H : SimpleGraph (Fin 6))
    (h5 : ∀ t, H.IsNClique 3 t → (5 : Fin 6) ∈ t)
    (T : Finset (Finset (Fin 6)))
    (hT : ∀ t ∈ T, H.IsNClique 3 t)
    (hpw : (T : Set (Finset (Fin 6))).Pairwise (fun a b => (a ∩ b).card ≤ 1)) :
    T.card ≤ 2 := by
  have hcard2 : ∀ t ∈ T, (t.erase 5).card = 2 := by
    intro t ht
    have h3 : t.card = 3 := ((SimpleGraph.isNClique_iff H).mp (hT t ht)).2
    rw [Finset.card_erase_of_mem (h5 t (hT t ht)), h3]
  have hdisj : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → Disjoint (t.erase 5) (u.erase 5) := by
    intro t ht u hu htu
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have hpw' : (t ∩ u).card ≤ 1 := hpw ht hu htu
    have h5t : (5 : Fin 6) ∈ t := h5 t (hT t ht)
    have h5u : (5 : Fin 6) ∈ u := h5 u (hT u hu)
    have hxne : x ≠ 5 := Finset.ne_of_mem_erase hx1
    have hsub : ({x, 5} : Finset (Fin 6)) ⊆ t ∩ u := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase hx1, Finset.mem_of_mem_erase hx2⟩
      · exact Finset.mem_inter.mpr ⟨h5t, h5u⟩
    have h2 : ({x, 5} : Finset (Fin 6)).card = 2 := by
      rw [Finset.card_insert_of_notMem, Finset.card_singleton]
      simp [hxne]
    have := Finset.card_le_card hsub
    omega
  have hsum : (T.biUnion fun t => t.erase 5).card = T.card * 2 := by
    rw [Finset.card_biUnion]
    · rw [Finset.sum_congr rfl (fun u hu => hcard2 u hu), Finset.sum_const, Nat.nsmul_eq_mul]
    · intro a ha b hb hab
      exact hdisj a ha b hb hab
  have hsub2 : (T.biUnion fun t => t.erase 5) ⊆ (Finset.univ : Finset (Fin 6)).erase 5 := by
    intro x hx
    simp only [Finset.mem_biUnion] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hxt, Finset.mem_univ x⟩
  have hle : (T.biUnion fun t => t.erase 5).card ≤ 5 := by
    have := Finset.card_le_card hsub2
    simpa using this
  omega

lemma simple_graph_stable_two_packing_arbitrary_cover_counterexample_packing_number_le_two
    (H : SimpleGraph (Fin 6))
    (h5 : ∀ t, H.IsNClique 3 t → (5 : Fin 6) ∈ t) :
    simple_graph_triangle_packing_number H ≤ 2 := by
  rw [simple_graph_triangle_packing_number]
  refine csSup_le ⟨0, ∅, by simp, by simp, by simp⟩ ?_
  rintro n ⟨T, hT, hpw, rfl⟩
  exact simple_graph_stable_two_packing_arbitrary_cover_counterexample_card_le_two_of_packing
    H h5 T hT hpw

lemma simple_graph_stable_two_packing_arbitrary_cover_counterexample_packing_number_ge_two
    (H : SimpleGraph (Fin 6))
    (h5 : ∀ t, H.IsNClique 3 t → (5 : Fin 6) ∈ t)
    (T : Finset (Finset (Fin 6)))
    (hT : ∀ t ∈ T, H.IsNClique 3 t)
    (hpw : (T : Set (Finset (Fin 6))).Pairwise (fun a b => (a ∩ b).card ≤ 1))
    (hcard : T.card = 2) :
    2 ≤ simple_graph_triangle_packing_number H := by
  rw [simple_graph_triangle_packing_number]
  refine le_csSup ⟨2, ?_⟩ ⟨T, hT, hpw, hcard⟩
  rintro b ⟨T', h1, h2, rfl⟩
  exact simple_graph_stable_two_packing_arbitrary_cover_counterexample_card_le_two_of_packing
    H h5 T' h1 h2

lemma simple_graph_stable_two_packing_arbitrary_cover_counterexample_wheel_packing_number :
    simple_graph_triangle_packing_number
      simple_graph_stable_two_packing_arbitrary_cover_counterexample_wheel = 2 := by
  apply le_antisymm
  · exact simple_graph_stable_two_packing_arbitrary_cover_counterexample_packing_number_le_two _
      simple_graph_stable_two_packing_arbitrary_cover_counterexample_three_clique_contains_five
  · refine simple_graph_stable_two_packing_arbitrary_cover_counterexample_packing_number_ge_two _
      simple_graph_stable_two_packing_arbitrary_cover_counterexample_three_clique_contains_five
      {{0,1,5},{2,3,5}} ?_ ?_ (by decide)
    · decide
    · rw [simple_graph_stable_two_packing_arbitrary_cover_counterexample_set_pairwise_iff]; decide

lemma simple_graph_stable_two_packing_arbitrary_cover_counterexample_mem_edgeSet_iff {a b : Fin 6} :
    s(a,b) ∈ simple_graph_stable_two_packing_arbitrary_cover_counterexample_wheel.edgeSet ↔
      s(a,b) ∈ simple_graph_stable_two_packing_arbitrary_cover_counterexample_edges := by
  rw [SimpleGraph.mem_edgeSet]
  constructor
  · intro h; exact h.1
  · intro h
    refine ⟨h, ?_⟩
    intro hab
    exact (by decide : ∀ e ∈ simple_graph_stable_two_packing_arbitrary_cover_counterexample_edges,
      ¬ e.IsDiag) _ h (Sym2.mk_isDiag_iff.mpr hab)

lemma simple_graph_stable_two_packing_arbitrary_cover_counterexample_mem_edgeSet (e : Sym2 (Fin 6)) :
    e ∈ simple_graph_stable_two_packing_arbitrary_cover_counterexample_wheel.edgeSet ↔
      e ∈ simple_graph_stable_two_packing_arbitrary_cover_counterexample_edges :=
  Sym2.ind (fun a b =>
    simple_graph_stable_two_packing_arbitrary_cover_counterexample_mem_edgeSet_iff (a := a) (b := b)) e

lemma simple_graph_stable_two_packing_arbitrary_cover_counterexample_cover_aux :
    ∀ a b c : Fin 6,
      simple_graph_stable_two_packing_arbitrary_cover_counterexample_wheel.Adj a b →
      simple_graph_stable_two_packing_arbitrary_cover_counterexample_wheel.Adj a c →
      simple_graph_stable_two_packing_arbitrary_cover_counterexample_wheel.Adj b c →
    (∀ x ∈ s(0,4), x ∈ ({a, b, c} : Finset (Fin 6))) ∨
    (∀ x ∈ s(3,4), x ∈ ({a, b, c} : Finset (Fin 6))) ∨
    (∀ x ∈ s(1,5), x ∈ ({a, b, c} : Finset (Fin 6))) ∨
    (∀ x ∈ s(2,5), x ∈ ({a, b, c} : Finset (Fin 6))) := by decide

lemma simple_graph_stable_two_packing_arbitrary_cover_counterexample_cover (t : Finset (Fin 6))
    (ht : simple_graph_stable_two_packing_arbitrary_cover_counterexample_wheel.IsNClique 3 t) :
    ∃ e ∈ simple_graph_stable_two_packing_arbitrary_cover_counterexample_coverSet,
      ∀ x ∈ e, x ∈ t := by
  rw [SimpleGraph.is3Clique_iff] at ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht
  rcases simple_graph_stable_two_packing_arbitrary_cover_counterexample_cover_aux a b c hab hac hbc
    with h | h | h | h
  · exact ⟨s(0,4), by decide, h⟩
  · exact ⟨s(3,4), by decide, h⟩
  · exact ⟨s(1,5), by decide, h⟩
  · exact ⟨s(2,5), by decide, h⟩

lemma simple_graph_stable_two_packing_arbitrary_cover_counterexample_mem_encoding
    {t : Finset (Fin 6)} {a b : Fin 6} :
    s(a,b) ∈ finite_vertex_set_edge_encoding t ↔ a ∈ t ∧ b ∈ t ∧ a ≠ b := by
  rw [finite_vertex_set_edge_encoding, Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff]
  tauto

lemma simple_graph_stable_two_packing_arbitrary_cover_counterexample_packing_number_delete
    (e : Sym2 (Fin 6))
    (he : e ∈ simple_graph_stable_two_packing_arbitrary_cover_counterexample_wheel.edgeSet) :
    simple_graph_triangle_packing_number
        (simple_graph_stable_two_packing_arbitrary_cover_counterexample_wheel.deleteEdges {e}) =
      simple_graph_triangle_packing_number
        simple_graph_stable_two_packing_arbitrary_cover_counterexample_wheel := by
  have h5del : ∀ (e' : Sym2 (Fin 6)) (t : Finset (Fin 6)),
      (simple_graph_stable_two_packing_arbitrary_cover_counterexample_wheel.deleteEdges
        {e'}).IsNClique 3 t → (5 : Fin 6) ∈ t :=
    fun e' t ht => simple_graph_stable_two_packing_arbitrary_cover_counterexample_contains_five_of_le
      (SimpleGraph.deleteEdges_le _) t ht
  induction e using Sym2.ind with
  | _ a b =>
    have he' : s(a,b) ∈ simple_graph_stable_two_packing_arbitrary_cover_counterexample_edges :=
      simple_graph_stable_two_packing_arbitrary_cover_counterexample_mem_edgeSet_iff.mp he
    rw [simple_graph_stable_two_packing_arbitrary_cover_counterexample_wheel_packing_number]
    simp only [simple_graph_stable_two_packing_arbitrary_cover_counterexample_edges,
      Finset.mem_insert, Finset.mem_singleton] at he'
    rcases he' with h | h | h | h | h | h | h | h | h | h
    · rw [h]; refine le_antisymm
        (simple_graph_stable_two_packing_arbitrary_cover_counterexample_packing_number_le_two _
          (h5del _)) ?_
      refine simple_graph_stable_two_packing_arbitrary_cover_counterexample_packing_number_ge_two _
        (h5del _) {{2,3,5},{0,4,5}} ?_ ?_ (by decide)
      · decide
      · rw [simple_graph_stable_two_packing_arbitrary_cover_counterexample_set_pairwise_iff]; decide
    · rw [h]; refine le_antisymm
        (simple_graph_stable_two_packing_arbitrary_cover_counterexample_packing_number_le_two _
          (h5del _)) ?_
      refine simple_graph_stable_two_packing_arbitrary_cover_counterexample_packing_number_ge_two _
        (h5del _) {{2,3,5},{0,4,5}} ?_ ?_ (by decide)
      · decide
      · rw [simple_graph_stable_two_packing_arbitrary_cover_counterexample_set_pairwise_iff]; decide
    · rw [h]; refine le_antisymm
        (simple_graph_stable_two_packing_arbitrary_cover_counterexample_packing_number_le_two _
          (h5del _)) ?_
      refine simple_graph_stable_two_packing_arbitrary_cover_counterexample_packing_number_ge_two _
        (h5del _) {{1,2,5},{0,4,5}} ?_ ?_ (by decide)
      · decide
      · rw [simple_graph_stable_two_packing_arbitrary_cover_counterexample_set_pairwise_iff]; decide
    · rw [h]; refine le_antisymm
        (simple_graph_stable_two_packing_arbitrary_cover_counterexample_packing_number_le_two _
          (h5del _)) ?_
      refine simple_graph_stable_two_packing_arbitrary_cover_counterexample_packing_number_ge_two _
        (h5del _) {{2,3,5},{0,4,5}} ?_ ?_ (by decide)
      · decide
      · rw [simple_graph_stable_two_packing_arbitrary_cover_counterexample_set_pairwise_iff]; decide
    · rw [h]; refine le_antisymm
        (simple_graph_stable_two_packing_arbitrary_cover_counterexample_packing_number_le_two _
          (h5del _)) ?_
      refine simple_graph_stable_two_packing_arbitrary_cover_counterexample_packing_number_ge_two _
        (h5del _) {{1,2,5},{3,4,5}} ?_ ?_ (by decide)
      · decide
      · rw [simple_graph_stable_two_packing_arbitrary_cover_counterexample_set_pairwise_iff]; decide
    · rw [h]; refine le_antisymm
        (simple_graph_stable_two_packing_arbitrary_cover_counterexample_packing_number_le_two _
          (h5del _)) ?_
      refine simple_graph_stable_two_packing_arbitrary_cover_counterexample_packing_number_ge_two _
        (h5del _) {{1,2,5},{3,4,5}} ?_ ?_ (by decide)
      · decide
      · rw [simple_graph_stable_two_packing_arbitrary_cover_counterexample_set_pairwise_iff]; decide
    · rw [h]; refine le_antisymm
        (simple_graph_stable_two_packing_arbitrary_cover_counterexample_packing_number_le_two _
          (h5del _)) ?_
      refine simple_graph_stable_two_packing_arbitrary_cover_counterexample_packing_number_ge_two _
        (h5del _) {{2,3,5},{0,4,5}} ?_ ?_ (by decide)
      · decide
      · rw [simple_graph_stable_two_packing_arbitrary_cover_counterexample_set_pairwise_iff]; decide
    · rw [h]; refine le_antisymm
        (simple_graph_stable_two_packing_arbitrary_cover_counterexample_packing_number_le_two _
          (h5del _)) ?_
      refine simple_graph_stable_two_packing_arbitrary_cover_counterexample_packing_number_ge_two _
        (h5del _) {{0,1,5},{3,4,5}} ?_ ?_ (by decide)
      · decide
      · rw [simple_graph_stable_two_packing_arbitrary_cover_counterexample_set_pairwise_iff]; decide
    · rw [h]; refine le_antisymm
        (simple_graph_stable_two_packing_arbitrary_cover_counterexample_packing_number_le_two _
          (h5del _)) ?_
      refine simple_graph_stable_two_packing_arbitrary_cover_counterexample_packing_number_ge_two _
        (h5del _) {{1,2,5},{0,4,5}} ?_ ?_ (by decide)
      · decide
      · rw [simple_graph_stable_two_packing_arbitrary_cover_counterexample_set_pairwise_iff]; decide
    · rw [h]; refine le_antisymm
        (simple_graph_stable_two_packing_arbitrary_cover_counterexample_packing_number_le_two _
          (h5del _)) ?_
      refine simple_graph_stable_two_packing_arbitrary_cover_counterexample_packing_number_ge_two _
        (h5del _) {{0,1,5},{2,3,5}} ?_ ?_ (by decide)
      · decide
      · rw [simple_graph_stable_two_packing_arbitrary_cover_counterexample_set_pairwise_iff]; decide

theorem simple_graph_stable_two_packing_arbitrary_cover_counterexample :
    ∃ (G : SimpleGraph (Fin 6)) (P : Finset (Finset (Fin 6)))
      (C : Finset (Sym2 (Fin 6))),
      simple_graph_triangle_packing_number G = 2 ∧
      (∀ e ∈ G.edgeSet,
        simple_graph_triangle_packing_number (G.deleteEdges {e}) =
          simple_graph_triangle_packing_number G) ∧
      (∀ t ∈ P, G.IsNClique 3 t) ∧
      (P : Set (Finset (Fin 6))).Pairwise (fun a b => (a ∩ b).card ≤ 1) ∧
      P.card = simple_graph_triangle_packing_number G ∧
      (∀ e ∈ C, e ∈ G.edgeSet) ∧
      (∀ t : Finset (Fin 6), G.IsNClique 3 t → ∃ e ∈ C, ∀ x ∈ e, x ∈ t) ∧
      C.card = 4 ∧
      ∀ Q : Finset (Finset (Fin 6)),
        (∀ t ∈ Q, G.IsNClique 3 t) →
        (Q : Set (Finset (Fin 6))).Pairwise (fun a b => (a ∩ b).card ≤ 1) →
        Q.card = simple_graph_triangle_packing_number G →
        ¬ C ⊆ (P.image finite_vertex_set_edge_encoding).biUnion id ∪
          (Q.image finite_vertex_set_edge_encoding).biUnion id := by
  refine ⟨simple_graph_stable_two_packing_arbitrary_cover_counterexample_wheel,
    {{0,1,5},{2,3,5}}, simple_graph_stable_two_packing_arbitrary_cover_counterexample_coverSet,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact simple_graph_stable_two_packing_arbitrary_cover_counterexample_wheel_packing_number
  · intro e he
    exact simple_graph_stable_two_packing_arbitrary_cover_counterexample_packing_number_delete e he
  · decide
  · rw [simple_graph_stable_two_packing_arbitrary_cover_counterexample_set_pairwise_iff]; decide
  · rw [simple_graph_stable_two_packing_arbitrary_cover_counterexample_wheel_packing_number]; decide
  · simp only [simple_graph_stable_two_packing_arbitrary_cover_counterexample_mem_edgeSet]
    decide
  · intro t ht
    exact simple_graph_stable_two_packing_arbitrary_cover_counterexample_cover t ht
  · decide
  · intro Q hQ hpw hcard hsub
    have h04C : s(0,4) ∈ simple_graph_stable_two_packing_arbitrary_cover_counterexample_coverSet :=
      by decide
    have h34C : s(3,4) ∈ simple_graph_stable_two_packing_arbitrary_cover_counterexample_coverSet :=
      by decide
    have h04P : s(0,4) ∉ (({{0,1,5},{2,3,5}} : Finset (Finset (Fin 6))).image
        finite_vertex_set_edge_encoding).biUnion id := by decide
    have h34P : s(3,4) ∉ (({{0,1,5},{2,3,5}} : Finset (Finset (Fin 6))).image
        finite_vertex_set_edge_encoding).biUnion id := by decide
    have h04 := hsub h04C
    rw [Finset.mem_union] at h04
    have h34 := hsub h34C
    rw [Finset.mem_union] at h34
    rcases h04 with h04 | h04
    · exact h04P h04
    · rcases h34 with h34 | h34
      · exact h34P h34
      · obtain ⟨u, hu, h04u⟩ := Finset.mem_biUnion.mp h04
        obtain ⟨t, htQ, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨u', hu', h34u⟩ := Finset.mem_biUnion.mp h34
        obtain ⟨t', ht'Q, rfl⟩ := Finset.mem_image.mp hu'
        have h04' := simple_graph_stable_two_packing_arbitrary_cover_counterexample_mem_encoding.mp h04u
        have h34' := simple_graph_stable_two_packing_arbitrary_cover_counterexample_mem_encoding.mp h34u
        obtain ⟨h0t, h4t, -⟩ := h04'
        obtain ⟨h3t', h4t', -⟩ := h34'
        have h5t : (5 : Fin 6) ∈ t :=
          simple_graph_stable_two_packing_arbitrary_cover_counterexample_three_clique_contains_five
            t (hQ t htQ)
        have h5t' : (5 : Fin 6) ∈ t' :=
          simple_graph_stable_two_packing_arbitrary_cover_counterexample_three_clique_contains_five
            t' (hQ t' ht'Q)
        have hct : t.card = 3 := ((SimpleGraph.isNClique_iff
          simple_graph_stable_two_packing_arbitrary_cover_counterexample_wheel).mp (hQ t htQ)).2
        have hct' : t'.card = 3 := ((SimpleGraph.isNClique_iff
          simple_graph_stable_two_packing_arbitrary_cover_counterexample_wheel).mp (hQ t' ht'Q)).2
        have ht_eq : t = {0,4,5} := by
          have hsubst : ({0,4,5} : Finset (Fin 6)) ⊆ t := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl
            · exact h0t
            · exact h4t
            · exact h5t
          have hc : ({0,4,5} : Finset (Fin 6)).card = 3 := by decide
          exact (Finset.eq_of_subset_of_card_le hsubst (by omega)).symm
        have ht'_eq : t' = {3,4,5} := by
          have hsubst : ({3,4,5} : Finset (Fin 6)) ⊆ t' := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl
            · exact h3t'
            · exact h4t'
            · exact h5t'
          have hc : ({3,4,5} : Finset (Fin 6)).card = 3 := by decide
          exact (Finset.eq_of_subset_of_card_le hsubst (by omega)).symm
        have hne : t' ≠ t := by rw [ht'_eq, ht_eq]; decide
        have hpw' := hpw ht'Q htQ hne
        rw [ht'_eq, ht_eq] at hpw'
        exact absurd hpw' (by decide)
