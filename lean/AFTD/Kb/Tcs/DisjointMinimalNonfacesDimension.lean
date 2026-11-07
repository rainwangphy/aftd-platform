import AFTD.Prelude
import AFTD.Kb.Tcs.SimplicialIsPure
import AFTD.Kb.Tcs.SimplicialDualGraph
import AFTD.Kb.Tcs.SimplicialIsMinimalNonface
import AFTD.Kb.Tcs.SimplicialIsFacet

/-!
# disjoint_minimal_nonfaces_dimension

Topic: combinatorics   Node: 8a821d3ab5d9

Provenance: helper lemma. arXiv:2611.08071 Lemma 5.1 and Corollary 5.2

Let Δ be an abstract simplicial complex on an n-element vertex set V, pure of facet size d, with connected dual graph. If its minimal nonfaces are pairwise disjoint and there are s of them, then d = n - s.
-/

/-- Dimension formula for simplicial complexes with pairwise disjoint minimal nonfaces. -/
theorem disjoint_minimal_nonfaces_dimension {V : Type*} [DecidableEq V] [Fintype V] (Δ : AbstractSimplicialComplex V) (n d s : ℕ) (hn : Fintype.card V = n) (hpure : simplicial_is_pure Δ d) (hconn : (simplicial_dual_graph Δ d).Connected) (M_set : Finset (Finset V)) (hs : M_set.card = s) (hM_all : ∀ M, simplicial_is_minimal_nonface Δ M ↔ M ∈ M_set) (hM_disj : ∀ M₁ ∈ M_set, ∀ M₂ ∈ M_set, M₁ ≠ M₂ → Disjoint M₁ M₂) : d = n - s := by
  classical
  -- a facet exists because the dual graph is connected
  obtain ⟨⟨G, hGfacet⟩⟩ := hconn.nonempty
  have hGcard : G.card = d := hpure G hGfacet
  have hGmem : G ∈ Δ.faces := hGfacet.1
  have hGmax : ∀ H ∈ Δ.faces, G ⊆ H → G = H := hGfacet.2
  -- faces are closed under nonempty subsets
  have hlower : ∀ {a b : Finset V}, a ∈ Δ.faces → b ⊆ a → b.Nonempty → b ∈ Δ.faces :=
    fun {a b} ha hba hb => (Δ.isRelLowerSet_faces ha).2 hba hb
  rcases Finset.eq_empty_or_nonempty (Finset.univ : Finset V) with huniv | huniv
  · -- degenerate case: no vertices
    have hEmpty : IsEmpty V := Finset.univ_eq_empty_iff.mp huniv
    have hd0 : d = 0 := by
      rw [← hGcard, Finset.card_eq_zero, ← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨x, -⟩
      exact hEmpty.false x
    have hn0 : n = 0 := by
      rw [← hn]
      exact Fintype.card_eq_zero_iff.mpr hEmpty
    have hs0 : s = 0 := by
      have hMs : M_set = ∅ := by
        rw [← Finset.not_nonempty_iff_eq_empty]
        rintro ⟨M, hM⟩
        have h2 : 2 ≤ M.card := ((hM_all M).mpr hM).1
        have hMe : M = ∅ := by
          rw [← Finset.not_nonempty_iff_eq_empty]
          rintro ⟨x, -⟩
          exact hEmpty.false x
        rw [hMe] at h2
        simp at h2
      rw [← hs, hMs]
      simp
    omega
  · -- main case: `d ≥ 1` because facets are nonempty
    have hd1 : 1 ≤ d := by
      have hpos : 0 < G.card := by
        by_contra h
        have hz : G.card = 0 := by omega
        have hGe : G = ∅ := Finset.card_eq_zero.mp hz
        obtain ⟨v, -⟩ := huniv
        have hv : ({v} : Finset V) ∈ Δ.faces := Δ.singleton_mem v
        have hsub : G ⊆ {v} := by rw [hGe]; exact Finset.empty_subset _
        have heq : G = {v} := hGmax {v} hv hsub
        have hc : ({v} : Finset V).card = 0 := by rw [← heq, hGe]; simp
        rw [Finset.card_singleton] at hc
        omega
      omega
    -- (A) every nonface with at least two vertices contains a minimal nonface
    have hmin_exists : ∀ N : Finset V, N ∉ Δ.faces → 2 ≤ N.card →
        ∃ M : Finset V, simplicial_is_minimal_nonface Δ M ∧ M ⊆ N := by
      intro N hN hN2
      have hne : (Finset.univ.filter (fun M : Finset V =>
          M ⊆ N ∧ M ∉ Δ.faces ∧ 2 ≤ M.card)).Nonempty :=
        ⟨N, by simp [hN, hN2]⟩
      obtain ⟨M, hMmem, hMmin⟩ := Finset.exists_min_image
        (Finset.univ.filter (fun M : Finset V => M ⊆ N ∧ M ∉ Δ.faces ∧ 2 ≤ M.card))
        (fun M => M.card) hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hMmem
      obtain ⟨hMN, hMnotface, hM2⟩ := hMmem
      refine ⟨M, ⟨hM2, hMnotface, ?_⟩, hMN⟩
      intro T hTM hTne
      by_contra hTnotface
      have hT2 : 2 ≤ T.card := by
        have hpos : 0 < T.card := Finset.card_pos.mpr hTne
        have hne1 : T.card ≠ 1 := by
          intro h1
          obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp h1
          exact hTnotface (Δ.singleton_mem x)
        omega
      have hTfilt : T ∈ Finset.univ.filter
          (fun M : Finset V => M ⊆ N ∧ M ∉ Δ.faces ∧ 2 ≤ M.card) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hTM.subset.trans hMN, hTnotface, hT2⟩
      have hle := hMmin T hTfilt
      have hlt : T.card < M.card := Finset.card_lt_card hTM
      omega
    -- (B) adding a vertex outside a facet always produces a nonface
    have hfac_insert : ∀ (H : Finset V) (v : V), simplicial_is_facet Δ H → v ∉ H →
        H ∪ {v} ∉ Δ.faces := by
      intro H v hH hv hmem
      have heq : H = H ∪ {v} := hH.2 _ hmem Finset.subset_union_left
      have hv1 : v ∈ H ∪ {v} := Finset.mem_union_right H (Finset.mem_singleton_self v)
      rw [← heq] at hv1
      exact hv hv1
    -- (C) every vertex outside a facet lies in a minimal nonface contained in
    -- the facet together with that vertex
    have hcover : ∀ (H : Finset V) (v : V), simplicial_is_facet Δ H → v ∉ H →
        ∃ M ∈ M_set, v ∈ M ∧ M ⊆ H ∪ {v} := by
      intro H v hH hv
      have hnotface : H ∪ {v} ∉ Δ.faces := hfac_insert H v hH hv
      have hHcard : H.card = d := hpure H hH
      have hcard2 : 2 ≤ (H ∪ {v}).card := by
        have h1 : (H ∪ {v}).card = H.card + 1 :=
          Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hv)
        rw [h1, hHcard]
        exact Nat.add_le_add_right hd1 1
      obtain ⟨M, hMmin, hMH⟩ := hmin_exists (H ∪ {v}) hnotface hcard2
      have hMmem : M ∈ M_set := (hM_all M).mp hMmin
      have hM2 : 2 ≤ M.card := hMmin.1
      have hMnotface : M ∉ Δ.faces := hMmin.2.1
      have hMpos : 0 < M.card := by omega
      have hMnotsub : ¬ M ⊆ H := fun hsub =>
        hMnotface (hlower hH.1 hsub (Finset.card_pos.mp hMpos))
      obtain ⟨x, hxM, hxH⟩ := Finset.not_subset.mp hMnotsub
      have hx : x ∈ H ∪ {v} := hMH hxM
      rw [Finset.mem_union] at hx
      have hvM : v ∈ M := by
        rcases hx with h | h
        · exact absurd h hxH
        · rw [Finset.mem_singleton] at h
          rw [h] at hxM
          exact hxM
      exact ⟨M, hMmem, hvM, hMH⟩
    -- (D) each minimal nonface contributes exactly one vertex outside `G`
    have huniq : ∀ M ∈ M_set, ∃ v : V, M \ G = {v} := by
      intro M hM
      have hM2 : 2 ≤ M.card := ((hM_all M).mpr hM).1
      have hMnotface : M ∉ Δ.faces := ((hM_all M).mpr hM).2.1
      have hMpos : 0 < M.card := by omega
      have hMnotsub : ¬ M ⊆ G := fun hsub =>
        hMnotface (hlower hGmem hsub (Finset.card_pos.mp hMpos))
      obtain ⟨v, hvM, hvG⟩ := Finset.not_subset.mp hMnotsub
      refine ⟨v, ?_⟩
      apply Finset.Subset.antisymm
      · intro x hx
        rw [Finset.mem_sdiff] at hx
        obtain ⟨hxM, hxG⟩ := hx
        obtain ⟨M', hM', hxM', hM'sub⟩ := hcover G x hGfacet hxG
        have hM'eq : M' = M := by
          by_contra hne
          have hd := hM_disj M' hM' M hM hne
          exact (Finset.disjoint_left.mp hd) hxM' hxM
        rw [hM'eq] at hM'sub
        have hv' : v ∈ G ∪ {x} := hM'sub hvM
        rw [Finset.mem_union] at hv'
        rcases hv' with h | h
        · exact absurd h hvG
        · rw [Finset.mem_singleton] at h
          rw [Finset.mem_singleton]
          exact h.symm
      · intro x hx
        rw [Finset.mem_singleton] at hx
        rw [hx]
        exact Finset.mem_sdiff.mpr ⟨hvM, hvG⟩
    have hcard_one : ∀ M ∈ M_set, (M \ G).card = 1 := by
      intro M hM
      obtain ⟨v, hv⟩ := huniq M hM
      rw [hv, Finset.card_singleton]
    -- the complement of a facet is the disjoint union of these singletons
    have hVF : (Finset.univ \ G) = M_set.biUnion (fun M => M \ G) := by
      apply Finset.Subset.antisymm
      · intro x hx
        rw [Finset.mem_sdiff] at hx
        obtain ⟨-, hxG⟩ := hx
        obtain ⟨M, hM, hxM, -⟩ := hcover G x hGfacet hxG
        exact Finset.mem_biUnion.mpr ⟨M, hM, Finset.mem_sdiff.mpr ⟨hxM, hxG⟩⟩
      · intro x hx
        obtain ⟨M, hM, hxM⟩ := Finset.mem_biUnion.mp hx
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hxM).2⟩
    have hcardVF : (Finset.univ \ G).card = s := by
      rw [hVF, Finset.card_biUnion (fun M hM M' hM' hne =>
        (hM_disj M hM M' hM' hne).mono Finset.sdiff_subset Finset.sdiff_subset)]
      rw [Finset.sum_congr rfl hcard_one]
      simp [hs]
    have hsum := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ G)
    rw [hcardVF, hGcard, Finset.card_univ, hn] at hsum
    omega
