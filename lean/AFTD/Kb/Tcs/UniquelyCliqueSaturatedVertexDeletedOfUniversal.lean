import AFTD.Prelude
import AFTD.Kb.Tcs.IsUniquelyCliqueSaturated

/-!
# uniquely_clique_saturated_vertex_deleted_of_universal

Topic: graphs   Node: 07186fa3cd1e

Provenance: helper lemma. arXiv:2611.13656 Proposition 2.1 (i)

Let r ≥ 3 be an integer, and let G be a finite simple graph. If G is uniquely K_r-saturated and x is a universal vertex of G, then the vertex-deleted subgraph G - x is uniquely K_{r-1}-saturated.
-/

/-- Deleting a universal vertex from a uniquely K_r-saturated graph yields a uniquely K_{r-1}-saturated graph. -/
theorem uniquely_clique_saturated_vertex_deleted_of_universal
    {V : Type*} [Fintype V] (G : SimpleGraph V) {r : ℕ} (hr : 3 ≤ r)
    (hG : is_uniquely_clique_saturated G r)
    (x : V) (hx : G.IsUniversal x) :
    is_uniquely_clique_saturated (G.induce (Set.univ \ {x})) (r - 1) := by
  classical
  rw [is_uniquely_clique_saturated] at hG ⊢
  obtain ⟨hno, huniq⟩ := hG
  let φ : ↥(Set.univ \ ({x} : Set V)) ↪ V :=
    Function.Embedding.subtype (fun v => v ∈ (Set.univ \ ({x} : Set V)))
  have hanx : ∀ (a : ↥(Set.univ \ ({x} : Set V))), (a:V) ≠ x := fun a => by
    simpa using a.property.2
  constructor
  · intro s hs
    rw [SimpleGraph.isNClique_iff] at hs
    obtain ⟨hclique, hcard⟩ := hs
    have h1 : (SimpleGraph.map (⇑φ) (G.induce (Set.univ \ ({x} : Set V)))).IsClique (⇑φ '' ↑s) :=
      SimpleGraph.IsClique.map hclique (f := φ)
    have hle : SimpleGraph.map (⇑φ) (G.induce (Set.univ \ ({x} : Set V))) ≤ G := by
      intro a b hab
      rw [SimpleGraph.map_adj] at hab
      obtain ⟨a', b', hadj, ha, hb⟩ := hab
      rw [← ha, ← hb]
      exact (SimpleGraph.induce_adj).mp hadj
    have h2 : G.IsClique (⇑φ '' ↑s) := SimpleGraph.IsClique.mono hle h1
    rw [← Finset.coe_map] at h2
    have hxnotmem : x ∉ s.map φ := by
      rw [Finset.mem_map]
      rintro ⟨a, ha, hax⟩
      exact (hanx a) hax
    have hcard' : (s.map φ).card = r - 1 := by rw [Finset.card_map, hcard]
    have h3 : G.IsClique (↑(insert x (s.map φ)) : Set V) := by
      rw [Finset.coe_insert]
      rw [SimpleGraph.isClique_insert]
      refine ⟨h2, ?_⟩
      intro b hb hxb
      exact hx hxb
    have h4 : (insert x (s.map φ)).card = r := by
      rw [Finset.card_insert_of_notMem hxnotmem, hcard']
      omega
    exact hno _ (by rw [SimpleGraph.isNClique_iff]; exact ⟨h3, h4⟩)
  · intro e
    induction e using Sym2.ind with
    | _ a b =>
      intro hab
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj] at hab
      obtain ⟨habne, habnotadj⟩ := hab
      have hGnotadj : ¬ G.Adj (a:V) (b:V) := by
        simpa only [SimpleGraph.induce_adj] using habnotadj
      have hne' : (a:V) ≠ (b:V) := fun h => habne (φ.injective h)
      have he' : s((a:V),(b:V)) ∈ Gᶜ.edgeSet := by
        rw [SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj]
        exact ⟨hne', hGnotadj⟩
      obtain ⟨S, hS, hSuniq⟩ := huniq _ he'
      rw [SimpleGraph.isNClique_iff] at hS
      obtain ⟨hS_clique, hS_card⟩ := hS
      have key : ∀ u v : ↥(Set.univ \ ({x} : Set V)),
          ((G.induce (Set.univ \ ({x} : Set V))) ⊔ SimpleGraph.fromEdgeSet {s(a,b)}).Adj u v ↔
          (G ⊔ SimpleGraph.fromEdgeSet {s((a:V),(b:V))}).Adj (u:V) (v:V) := by
        intro u v
        rw [SimpleGraph.sup_adj, SimpleGraph.sup_adj]
        constructor
        · rintro (h | h)
          · left; exact (SimpleGraph.induce_adj).mp h
          · right
            rw [SimpleGraph.fromEdgeSet_adj] at h ⊢
            obtain ⟨hmem, hne⟩ := h
            refine ⟨?_, ?_⟩
            · simp only [Set.mem_singleton_iff] at hmem ⊢
              rw [← Sym2.map_mk (Subtype.val) u v, ← Sym2.map_mk (Subtype.val) a b]
              exact congrArg (Sym2.map (Subtype.val : ↥(Set.univ \ ({x} : Set V)) → V)) hmem
            · exact fun hh => hne (Subtype.val_injective hh)
        · rintro (h | h)
          · left; exact (SimpleGraph.induce_adj).mpr h
          · right
            rw [SimpleGraph.fromEdgeSet_adj] at h ⊢
            obtain ⟨hmem, hne⟩ := h
            refine ⟨?_, ?_⟩
            · rw [Set.mem_singleton_iff] at hmem
              rw [Set.mem_singleton_iff, Sym2.eq_iff]
              rw [Sym2.eq_iff] at hmem
              rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact Or.inl ⟨Subtype.val_injective h1, Subtype.val_injective h2⟩
              · exact Or.inr ⟨Subtype.val_injective h1, Subtype.val_injective h2⟩
            · exact fun hh => hne (congrArg Subtype.val hh)
      have clique_iff : ∀ s : Finset ↥(Set.univ \ ({x} : Set V)),
          ((G.induce (Set.univ \ ({x} : Set V))) ⊔ SimpleGraph.fromEdgeSet {s(a,b)}).IsClique (↑s) ↔
          (G ⊔ SimpleGraph.fromEdgeSet {s((a:V),(b:V))}).IsClique (↑(s.map φ)) := by
        intro s
        rw [SimpleGraph.isClique_iff, SimpleGraph.isClique_iff]
        constructor
        · intro h p hp q hq hpq
          rw [Finset.mem_coe, Finset.mem_map] at hp hq
          obtain ⟨u, hu, rfl⟩ := hp
          obtain ⟨v, hv, rfl⟩ := hq
          have huv : u ≠ v := fun hc => hpq (by rw [hc])
          exact (key u v).mp (h (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hv) huv)
        · intro h u hu v hv huv
          rw [Finset.mem_coe] at hu hv
          exact (key u v).mpr
            (h (Finset.mem_coe.mpr ((Finset.mem_map).mpr ⟨u, hu, rfl⟩))
               (Finset.mem_coe.mpr ((Finset.mem_map).mpr ⟨v, hv, rfl⟩))
               (fun hc => huv (φ.injective hc)))
      have nclique_iff : ∀ s : Finset ↥(Set.univ \ ({x} : Set V)),
          ((G.induce (Set.univ \ ({x} : Set V))) ⊔ SimpleGraph.fromEdgeSet {s(a,b)}).IsNClique (r-1) s ↔
          (G ⊔ SimpleGraph.fromEdgeSet {s((a:V),(b:V))}).IsNClique (r-1) (s.map φ) := by
        intro s
        rw [SimpleGraph.isNClique_iff, SimpleGraph.isNClique_iff, clique_iff s, Finset.card_map]
      have hxS : x ∈ S := by
        by_contra hxS
        have hSpos : 0 < S.card := by rw [hS_card]; omega
        obtain ⟨c, hcS⟩ := Finset.card_pos.mp hSpos
        have hc' : x ∉ S.erase c := by simp [hxS]
        have hS'_clique : (G ⊔ SimpleGraph.fromEdgeSet {s((a:V),(b:V))}).IsClique (↑(insert x (S.erase c)) : Set V) := by
          rw [Finset.coe_insert, SimpleGraph.isClique_insert]
          refine ⟨?_, ?_⟩
          · apply SimpleGraph.IsClique.subset _ hS_clique
            intro y hy
            rw [Finset.coe_erase] at hy
            exact hy.1
          · intro y hy hxy
            rw [SimpleGraph.sup_adj]
            exact Or.inl (hx hxy)
        have hS'_card : (insert x (S.erase c)).card = r := by
          rw [Finset.card_insert_of_notMem hc', Finset.card_erase_of_mem hcS, hS_card]
          omega
        have hS' : (G ⊔ SimpleGraph.fromEdgeSet {s((a:V),(b:V))}).IsNClique r (insert x (S.erase c)) := by
          rw [SimpleGraph.isNClique_iff]; exact ⟨hS'_clique, hS'_card⟩
        have huniqS := hSuniq _ hS'
        have : x ∈ S := by rw [← huniqS]; exact Finset.mem_insert_self x _
        exact hxS this
      let p : V → Prop := fun v => v ∈ (Set.univ \ ({x} : Set V))
      let t : Finset ↥(Set.univ \ ({x} : Set V)) := Finset.subtype p (S.erase x)
      have hfilt : Finset.filter p (S.erase x) = S.erase x := by
        apply Finset.filter_true_of_mem
        intro y hy
        rw [Finset.mem_erase] at hy
        obtain ⟨hyx, hyS⟩ := hy
        simp only [p, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
        exact hyx
      have ht_map : t.map φ = S.erase x := by
        have h := Finset.subtype_map p (s := S.erase x)
        rw [hfilt] at h
        exact h
      have ht : ((G.induce (Set.univ \ ({x} : Set V))) ⊔ SimpleGraph.fromEdgeSet {s(a,b)}).IsNClique (r-1) t := by
        rw [nclique_iff t, ht_map, SimpleGraph.isNClique_iff]
        refine ⟨?_, ?_⟩
        · apply SimpleGraph.IsClique.subset _ hS_clique
          intro y hy
          rw [Finset.coe_erase] at hy
          exact hy.1
        · rw [Finset.card_erase_of_mem hxS, hS_card]
      refine ⟨t, ht, ?_⟩
      intro t' ht'
      have ht'_map : (G ⊔ SimpleGraph.fromEdgeSet {s((a:V),(b:V))}).IsNClique (r-1) (t'.map φ) :=
        (nclique_iff t').mp ht'
      have hx_notin : x ∉ t'.map φ := by
        rw [Finset.mem_map]
        rintro ⟨a', ha', hax⟩
        exact (hanx a') hax
      have hT'_clique : (G ⊔ SimpleGraph.fromEdgeSet {s((a:V),(b:V))}).IsClique (↑(insert x (t'.map φ)) : Set V) := by
        rw [Finset.coe_insert, SimpleGraph.isClique_insert]
        refine ⟨ht'_map.1, ?_⟩
        intro y hy hxy
        rw [SimpleGraph.sup_adj]
        exact Or.inl (hx hxy)
      have hT'_card : (insert x (t'.map φ)).card = r := by
        rw [Finset.card_insert_of_notMem hx_notin]
        have h := ht'_map.2
        omega
      have hT' : (G ⊔ SimpleGraph.fromEdgeSet {s((a:V),(b:V))}).IsNClique r (insert x (t'.map φ)) := by
        rw [SimpleGraph.isNClique_iff]; exact ⟨hT'_clique, hT'_card⟩
      have hEq : insert x (t'.map φ) = S := hSuniq _ hT'
      have ht'_map2 : t'.map φ = S.erase x := by
        rw [← hEq, Finset.erase_insert hx_notin]
      rw [← ht_map] at ht'_map2
      exact Finset.map_injective φ ht'_map2
