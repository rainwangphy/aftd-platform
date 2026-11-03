import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumber
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# simple_graph_triangle_cover_number_le_two_mul_packing_of_local_certificate

Topic: graphs   Node: d0bee2ed69af

Provenance: helper lemma. Related work: arXiv:2610.15269, Definition 2.1 and Lemma 2.2. This is the general packing-extension implication underpinning the local reduction framework.

Let H be a subgraph of a finite graph G. If a triangle packing S in G is edge-disjoint from every triangle in H, and an edge set X of size at most twice |S| covers every triangle of G not present in H, then the triangle cover-packing inequality for H implies it for G.
-/

theorem simple_graph_triangle_cover_number_le_two_mul_packing_of_local_certificate
    {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (hsub : H ≤ G)
    (S : Finset (Finset V)) (X : Finset (Sym2 V))
    (hs : ∀ s ∈ S, G.IsNClique 3 s)
    (hsp : (S : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1))
    (hsep : ∀ s ∈ S, ∀ t : Finset V, H.IsNClique 3 t → (s ∩ t).card ≤ 1)
    (hx : ∀ e ∈ X, e ∈ G.edgeSet)
    (hcover : ∀ t : Finset V, G.IsNClique 3 t →
      H.IsNClique 3 t ∨ ∃ e ∈ X, ∀ x ∈ e, x ∈ t)
    (hbudget : X.card ≤ 2 * S.card)
    (hind : simple_graph_triangle_cover_number H ≤ 2 * simple_graph_triangle_packing_number H) :
    simple_graph_triangle_cover_number G ≤ 2 * simple_graph_triangle_packing_number G := by
  classical
  set P : Set ℕ := {n | ∃ T : Finset (Finset V), (∀ t ∈ T, H.IsNClique 3 t) ∧
    (T : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1) ∧ T.card = n}
  have hpne : P.Nonempty := ⟨0, ∅, by simp, by simp, rfl⟩
  have hpbound : BddAbove P := by
    refine ⟨Fintype.card (Finset V), ?_⟩
    rintro n ⟨T, -, -, rfl⟩
    exact Finset.card_le_univ T
  obtain ⟨T, ht, htp, htcard⟩ := Nat.sSup_mem hpne hpbound
  have hstdisj : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro s hsS hsT
    have hc := hsep s hsS s (ht s hsT)
    rw [Finset.inter_self, (hs s hsS).card_eq] at hc
    omega
  have htpair : ((S ∪ T : Finset (Finset V)) : Set (Finset V)).Pairwise
      (fun s t => (s ∩ t).card ≤ 1) := by
    rw [Finset.coe_union, Set.pairwise_union]
    refine ⟨hsp, htp, ?_⟩
    intro s hsS t htT _
    exact ⟨hsep s hsS t (ht t htT), by
      rw [Finset.inter_comm]
      exact hsep s hsS t (ht t htT)⟩
  have hsup : S.card + simple_graph_triangle_packing_number H ≤
      simple_graph_triangle_packing_number G := by
    unfold simple_graph_triangle_packing_number
    rw [← htcard, ← Finset.card_union_of_disjoint hstdisj]
    apply le_csSup
    · refine ⟨Fintype.card (Finset V), ?_⟩
      rintro n ⟨T', -, -, rfl⟩
      exact Finset.card_le_univ T'
    · refine ⟨S ∪ T, ?_, htpair, rfl⟩
      intro t htST
      rcases Finset.mem_union.mp htST with htS | htT
      · exact hs t htS
      · exact (ht t htT).mono hsub
  have hSne : {n : ℕ | ∃ F : Finset (Sym2 V), (∀ f ∈ F, f ∈ H.edgeSet) ∧
      (∀ t : Finset V, H.IsNClique 3 t → ∃ f ∈ F, ∀ x ∈ f, x ∈ t) ∧ F.card = n}.Nonempty := by
    refine ⟨_, H.edgeFinset, ?_, ?_, rfl⟩
    · intro f hf; rwa [SimpleGraph.mem_edgeFinset] at hf
    · intro t ht'
      obtain ⟨u, v, w, huv, -, -, rfl⟩ := Finset.card_eq_three.mp ht'.card_eq
      refine ⟨s(u, v), ?_, ?_⟩
      · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        exact ht'.isClique (by simp) (by simp) huv
      · intro x hx'
        rw [Sym2.mem_iff] at hx'
        rcases hx' with rfl | rfl <;> simp
  obtain ⟨F, hfsub, hfcov, hfcard⟩ := Nat.sInf_mem hSne
  change F.card = simple_graph_triangle_cover_number H at hfcard
  have hle : simple_graph_triangle_cover_number G ≤ F.card + X.card := by
    have hc : ∀ t : Finset V, G.IsNClique 3 t →
        ∃ e ∈ F ∪ X, ∀ x ∈ e, x ∈ t := by
      intro t ht'
      rcases hcover t ht' with htH | ⟨e, heX, he⟩
      · obtain ⟨e, heF, he⟩ := hfcov t htH
        exact ⟨e, Finset.mem_union_left X heF, he⟩
      · exact ⟨e, Finset.mem_union_right F heX, he⟩
    have he : ∀ e ∈ F ∪ X, e ∈ G.edgeSet := by
      intro e he'
      rcases Finset.mem_union.mp he' with heF | heX
      · exact SimpleGraph.edgeSet_mono hsub (hfsub e heF)
      · exact hx e heX
    have hmem : (F ∪ X).card ∈ {n : ℕ | ∃ F' : Finset (Sym2 V),
      (∀ e ∈ F', e ∈ G.edgeSet) ∧
      (∀ t : Finset V, G.IsNClique 3 t → ∃ e ∈ F', ∀ x ∈ e, x ∈ t) ∧ F'.card = n} :=
      ⟨F ∪ X, he, hc, rfl⟩
    exact (Nat.sInf_le hmem).trans (Finset.card_union_le F X)
  rw [hfcard] at hle
  omega
