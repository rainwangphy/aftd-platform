import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding

/-!
# simple_graph_triangle_packing_support_four_k_vertex_kernel

Topic: graphs   Node: c3ee42e700f0

Provenance: helper lemma. Support-signature compression for the triangle packing-cover campaign.

Let P be an edge-disjoint triangle family whose edge union meets every graph triangle. If each packed triangle has at most one singly supported edge, an induced subgraph on at most four times |P| vertices retains P and every triangle support signature relative to P.
-/

open Finset
open scoped Sym2

/-- An edge of the encoding of `s` has both endpoints in `s`. -/
private lemma simple_graph_triangle_packing_support_four_k_vertex_kernel_enc_sub
    {V : Type*} [DecidableEq V] {s : Finset V} {e : Sym2 V}
    (h : e ∈ finite_vertex_set_edge_encoding s) : e.toFinset ⊆ s := by
  intro x hx
  rw [Sym2.mem_toFinset] at hx
  exact (Finset.mem_sym2_iff.mp (Finset.mem_filter.mp h).1) x hx

/-- Edges of the encoding of `s` are off the diagonal. -/
private lemma simple_graph_triangle_packing_support_four_k_vertex_kernel_not_diag
    {V : Type*} [DecidableEq V] {s : Finset V} {e : Sym2 V}
    (h : e ∈ finite_vertex_set_edge_encoding s) : ¬ e.IsDiag :=
  (Finset.mem_filter.mp h).2

/-- An edge of the encoding of `s` spans exactly two vertices. -/
private lemma simple_graph_triangle_packing_support_four_k_vertex_kernel_card_two
    {V : Type*} [DecidableEq V] {s : Finset V} {e : Sym2 V}
    (h : e ∈ finite_vertex_set_edge_encoding s) : e.toFinset.card = 2 :=
  Sym2.card_toFinset_of_not_isDiag e
    (simple_graph_triangle_packing_support_four_k_vertex_kernel_not_diag h)

/-- Two off-diagonal edges with the same vertex set are equal. -/
private lemma simple_graph_triangle_packing_support_four_k_vertex_kernel_inj
    {V : Type*} [DecidableEq V] {e1 e2 : Sym2 V}
    (h1 : ¬ e1.IsDiag) (h : e1.toFinset = e2.toFinset) : e1 = e2 := by
  have hne : e1.out.1 ≠ e1.out.2 := by
    intro heq
    apply h1
    rw [← Quot.out_eq e1]
    rw [Sym2.mk_isDiag_iff]
    exact heq
  have hx2 : e1.out.1 ∈ e2 := by
    have hh : e1.out.1 ∈ e1.toFinset := by
      rw [Sym2.mem_toFinset]; exact Sym2.out_fst_mem e1
    rw [h] at hh
    rwa [Sym2.mem_toFinset] at hh
  have hy2 : e1.out.2 ∈ e2 := by
    have hh : e1.out.2 ∈ e1.toFinset := by
      rw [Sym2.mem_toFinset]; exact Sym2.out_snd_mem e1
    rw [h] at hh
    rwa [Sym2.mem_toFinset] at hh
  have key : e2 = s(e1.out.1, e1.out.2) := (Sym2.mem_and_mem_iff hne).mp ⟨hx2, hy2⟩
  rw [key]
  exact (Quot.out_eq e1).symm

/-- A triangle sharing one of its edges with a fixed set leaves at most one vertex outside it. -/
private lemma simple_graph_triangle_packing_support_four_k_vertex_kernel_sdiff_le_one
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {t p : Finset V} {e : Sym2 V}
    (ht : G.IsNClique 3 t) (het : e ∈ finite_vertex_set_edge_encoding t)
    (hep : e ∈ finite_vertex_set_edge_encoding p) : (t \ p).card ≤ 1 := by
  have hsub_t : e.toFinset ⊆ t :=
    simple_graph_triangle_packing_support_four_k_vertex_kernel_enc_sub het
  have hsub_p : e.toFinset ⊆ p :=
    simple_graph_triangle_packing_support_four_k_vertex_kernel_enc_sub hep
  have hce : e.toFinset.card = 2 :=
    simple_graph_triangle_packing_support_four_k_vertex_kernel_card_two het
  have hct : t.card = 3 := ht.card_eq
  have hsub : t \ p ⊆ t \ e.toFinset := by
    intro x hx
    rw [Finset.mem_sdiff] at hx ⊢
    exact ⟨hx.1, fun hxe => hx.2 (hsub_p hxe)⟩
  have hcle : (t \ e.toFinset).card ≤ 1 := by
    rw [Finset.card_sdiff_of_subset hsub_t]
    omega
  exact le_trans (Finset.card_le_card hsub) hcle

/-- Two distinct edges of a triangle already span all three of its vertices. -/
private lemma simple_graph_triangle_packing_support_four_k_vertex_kernel_union_eq
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {t : Finset V} {e1 e2 : Sym2 V}
    (ht : G.IsNClique 3 t)
    (he1 : e1 ∈ finite_vertex_set_edge_encoding t)
    (he2 : e2 ∈ finite_vertex_set_edge_encoding t) (hne : e1 ≠ e2) :
    t = e1.toFinset ∪ e2.toFinset := by
  have hsub1 : e1.toFinset ⊆ t :=
    simple_graph_triangle_packing_support_four_k_vertex_kernel_enc_sub he1
  have hsub2 : e2.toFinset ⊆ t :=
    simple_graph_triangle_packing_support_four_k_vertex_kernel_enc_sub he2
  have hcard1 : e1.toFinset.card = 2 :=
    simple_graph_triangle_packing_support_four_k_vertex_kernel_card_two he1
  have hcard2 : e2.toFinset.card = 2 :=
    simple_graph_triangle_packing_support_four_k_vertex_kernel_card_two he2
  have htcard : t.card = 3 := ht.card_eq
  have hne' : e1.toFinset ≠ e2.toFinset := by
    intro h
    exact hne (simple_graph_triangle_packing_support_four_k_vertex_kernel_inj
      (simple_graph_triangle_packing_support_four_k_vertex_kernel_not_diag he1) h)
  have hsubu : e1.toFinset ∪ e2.toFinset ⊆ t := Finset.union_subset hsub1 hsub2
  have hleu : (e1.toFinset ∪ e2.toFinset).card ≤ 3 := by
    have := Finset.card_le_card hsubu; omega
  have hinter : (e1.toFinset ∩ e2.toFinset).card ≤ 1 := by
    by_contra h
    rw [not_le] at h
    have hle : (e1.toFinset ∩ e2.toFinset).card ≤ e1.toFinset.card :=
      Finset.card_le_card Finset.inter_subset_left
    have heq1 : e1.toFinset ∩ e2.toFinset = e1.toFinset :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hsube : e1.toFinset ⊆ e2.toFinset := by rw [← heq1]; exact Finset.inter_subset_right
    exact hne' (Finset.eq_of_subset_of_card_le hsube (by omega))
  have hunion : (e1.toFinset ∪ e2.toFinset).card = 3 := by
    have h := Finset.card_union_add_card_inter e1.toFinset e2.toFinset
    omega
  exact (Finset.eq_of_subset_of_card_le hsubu (by omega)).symm

/-- The encoding of a finite vertex set has `choose 2` elements. -/
private lemma simple_graph_triangle_packing_support_four_k_vertex_kernel_card_choose
    {V : Type*} [DecidableEq V] (s : Finset V) :
    (finite_vertex_set_edge_encoding s).card = s.card.choose 2 := by
  have h1 : finite_vertex_set_edge_encoding s = s.offDiag.image Sym2.mk.uncurry := by
    rw [finite_vertex_set_edge_encoding, Finset.sym2_eq_image, Sym2.filter_image_mk_not_isDiag]
  rw [h1, Sym2.card_image_offDiag]

theorem simple_graph_triangle_packing_support_four_k_vertex_kernel
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset (Finset V))
    (hP : ∀ p ∈ P, G.IsNClique 3 p)
    (hpack : (P : Set (Finset V)).Pairwise (fun a b => (a ∩ b).card ≤ 1))
    (hcover : ∀ t : Finset V, G.IsNClique 3 t →
      ¬ Disjoint (finite_vertex_set_edge_encoding t)
        ((P.image finite_vertex_set_edge_encoding).biUnion id))
    (hforced : ∀ p ∈ P, ∀ e f : Sym2 V,
      e ∈ finite_vertex_set_edge_encoding p → f ∈ finite_vertex_set_edge_encoding p → e ≠ f →
      ¬ ((∃ t : Finset V, G.IsNClique 3 t ∧
            finite_vertex_set_edge_encoding t ∩ ((P.image finite_vertex_set_edge_encoding).biUnion id) = {e}) ∧
         (∃ t : Finset V, G.IsNClique 3 t ∧
            finite_vertex_set_edge_encoding t ∩ ((P.image finite_vertex_set_edge_encoding).biUnion id) = {f}))) :
    ∃ W : Finset V, W.card ≤ 4 * P.card ∧ P.biUnion id ⊆ W ∧
      ∀ t : Finset V, G.IsNClique 3 t → ∃ s : Finset V,
        G.IsNClique 3 s ∧ s ⊆ W ∧
        finite_vertex_set_edge_encoding s ∩ ((P.image finite_vertex_set_edge_encoding).biUnion id) =
          finite_vertex_set_edge_encoding t ∩ ((P.image finite_vertex_set_edge_encoding).biUnion id) := by
  classical
  set U := (P.image finite_vertex_set_edge_encoding).biUnion id with hUdef
  have hUmem : ∀ e : Sym2 V, e ∈ U ↔ ∃ p ∈ P, e ∈ finite_vertex_set_edge_encoding p := by
    intro e
    rw [hUdef, Finset.mem_biUnion]
    constructor
    · rintro ⟨a, ha, hea⟩
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
      exact ⟨p, hp, hea⟩
    · rintro ⟨p, hp, hep⟩
      exact ⟨_, Finset.mem_image.mpr ⟨p, hp, rfl⟩, hep⟩
  set witnessOf : Sym2 V → Finset V := fun e =>
    if h : ∃ t : Finset V, G.IsNClique 3 t ∧ finite_vertex_set_edge_encoding t ∩ U = {e}
    then Classical.choose h else ∅ with hwdef
  set extra : Finset V → Finset V := fun p =>
    if h : ∃ e, e ∈ finite_vertex_set_edge_encoding p ∧
        (∃ t : Finset V, G.IsNClique 3 t ∧ finite_vertex_set_edge_encoding t ∩ U = {e})
    then witnessOf (Classical.choose h) \ p else ∅ with hextradef
  have hwit : ∀ e : Sym2 V,
      (∃ t : Finset V, G.IsNClique 3 t ∧ finite_vertex_set_edge_encoding t ∩ U = {e}) →
      G.IsNClique 3 (witnessOf e) ∧ finite_vertex_set_edge_encoding (witnessOf e) ∩ U = {e} := by
    intro e h
    have hw : witnessOf e = Classical.choose h := by rw [hwdef]; exact dif_pos h
    rw [hw]
    exact Classical.choose_spec h
  have huniq : ∀ p ∈ P, ∀ e f : Sym2 V, e ∈ finite_vertex_set_edge_encoding p →
      f ∈ finite_vertex_set_edge_encoding p →
      (∃ t : Finset V, G.IsNClique 3 t ∧ finite_vertex_set_edge_encoding t ∩ U = {e}) →
      (∃ t : Finset V, G.IsNClique 3 t ∧ finite_vertex_set_edge_encoding t ∩ U = {f}) → e = f := by
    intro p hp e f he hf hse hsf
    by_contra hne
    exact hforced p hp e f he hf hne ⟨hse, hsf⟩
  have hextra : ∀ p ∈ P, ∀ e : Sym2 V, e ∈ finite_vertex_set_edge_encoding p →
      (∃ t : Finset V, G.IsNClique 3 t ∧ finite_vertex_set_edge_encoding t ∩ U = {e}) →
      extra p = witnessOf e \ p := by
    intro p hp e he hse
    have hex : ∃ e, e ∈ finite_vertex_set_edge_encoding p ∧
        (∃ t : Finset V, G.IsNClique 3 t ∧ finite_vertex_set_edge_encoding t ∩ U = {e}) := ⟨e, he, hse⟩
    have hEp : extra p = witnessOf (Classical.choose hex) \ p := by
      rw [hextradef]; exact dif_pos hex
    have hspec := Classical.choose_spec hex
    have heq : Classical.choose hex = e := huniq p hp _ e hspec.1 he hspec.2 hse
    rw [hEp, heq]
  have hextra_card : ∀ p ∈ P, (extra p).card ≤ 1 := by
    intro p hp
    by_cases hex : ∃ e, e ∈ finite_vertex_set_edge_encoding p ∧
        (∃ t : Finset V, G.IsNClique 3 t ∧ finite_vertex_set_edge_encoding t ∩ U = {e})
    · obtain ⟨e, he, hse⟩ := hex
      rw [hextra p hp e he hse]
      obtain ⟨hw3, hwenc⟩ := hwit e hse
      have hm1 : e ∈ finite_vertex_set_edge_encoding (witnessOf e) := by
        have hmem : e ∈ finite_vertex_set_edge_encoding (witnessOf e) ∩ U := by
          rw [hwenc]; exact Finset.mem_singleton_self _
        exact (Finset.mem_inter.mp hmem).1
      exact simple_graph_triangle_packing_support_four_k_vertex_kernel_sdiff_le_one hw3 hm1 he
    · have hz : extra p = ∅ := by rw [hextradef]; exact dif_neg hex
      rw [hz]; simp
  refine ⟨P.biUnion id ∪ P.biUnion extra, ?_, Finset.subset_union_left, ?_⟩
  · have hc1 : (P.biUnion id).card ≤ 3 * P.card := by
      have h := Finset.card_biUnion_le (s := P) (t := fun p => p)
      have h2 : ∑ p ∈ P, p.card = P.card * 3 := by
        rw [Finset.sum_congr rfl (fun p hp => (hP p hp).card_eq)]
        simp
      calc (P.biUnion id).card ≤ ∑ p ∈ P, p.card := h
        _ = P.card * 3 := h2
        _ = 3 * P.card := by ring
    have hc2 : (P.biUnion extra).card ≤ P.card := by
      have h := Finset.card_biUnion_le (s := P) (t := extra)
      have h3 : ∑ p ∈ P, (extra p).card ≤ P.card := by
        have h4 : ∑ p ∈ P, (extra p).card ≤ ∑ p ∈ P, (1 : ℕ) :=
          Finset.sum_le_sum (fun p hp => hextra_card p hp)
        have h5 : ∑ p ∈ P, (1 : ℕ) = P.card := by
          rw [Finset.sum_const_nat (fun p hp => rfl)]; omega
        omega
      omega
    have h := Finset.card_union_le (P.biUnion id) (P.biUnion extra)
    omega
  · intro t ht
    set sig := finite_vertex_set_edge_encoding t ∩ U with hsigdef
    have hne : sig.Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp (hcover t ht)
    have hsigcard : 0 < sig.card := Finset.card_pos.mpr hne
    have hUW : ∀ e ∈ U, e.toFinset ⊆ P.biUnion id ∪ P.biUnion extra := by
      intro e he
      obtain ⟨p, hp, hep⟩ := (hUmem e).mp he
      exact Finset.Subset.trans
        (simple_graph_triangle_packing_support_four_k_vertex_kernel_enc_sub hep)
        (Finset.Subset.trans (Finset.subset_biUnion_of_mem (fun p => p) hp) Finset.subset_union_left)
    rcases Nat.eq_or_lt_of_le hsigcard with hone | hgt
    · obtain ⟨e, hee⟩ := Finset.card_eq_one.mp hone.symm
      have hesig : e ∈ sig := by rw [hee]; exact Finset.mem_singleton_self e
      have heU : e ∈ U := (Finset.mem_inter.mp hesig).2
      have hse : ∃ t : Finset V, G.IsNClique 3 t ∧ finite_vertex_set_edge_encoding t ∩ U = {e} :=
        ⟨t, ht, by rw [← hsigdef]; exact hee⟩
      refine ⟨witnessOf e, (hwit e hse).1, ?_, ?_⟩
      · obtain ⟨p, hp, hep⟩ := (hUmem e).mp heU
        have hEp : extra p = witnessOf e \ p := hextra p hp e hep hse
        have h1 : witnessOf e ⊆ p ∪ extra p := by
          intro x hx
          by_cases hxp : x ∈ p
          · exact Finset.mem_union_left _ hxp
          · refine Finset.mem_union_right _ ?_
            rw [hEp]; exact Finset.mem_sdiff.mpr ⟨hx, hxp⟩
        refine Finset.Subset.trans h1 ?_
        exact Finset.union_subset
          (Finset.Subset.trans (Finset.subset_biUnion_of_mem (fun p => p) hp) Finset.subset_union_left)
          (Finset.Subset.trans (Finset.subset_biUnion_of_mem (fun p => extra p) hp)
            Finset.subset_union_right)
      · rw [(hwit e hse).2]
        exact hee.symm
    · obtain ⟨e1, he1, e2, he2, h12⟩ := Finset.one_lt_card.mp hgt
      have he1U : e1 ∈ U := (Finset.mem_inter.mp he1).2
      have he2U : e2 ∈ U := (Finset.mem_inter.mp he2).2
      have ht_eq : t = e1.toFinset ∪ e2.toFinset :=
        simple_graph_triangle_packing_support_four_k_vertex_kernel_union_eq ht
          (Finset.mem_inter.mp he1).1 (Finset.mem_inter.mp he2).1 h12
      refine ⟨t, ht, ?_, rfl⟩
      rw [ht_eq]
      exact Finset.union_subset (hUW e1 he1U) (hUW e2 he2U)
