import AFTD.Prelude

/-!
# balanced_cut_anticomplete_side_has_cross_matching

Topic: graphs   Node: f14663402966

Provenance: helper lemma. Balanced-cut separator matching for OP-1957; https://arxiv.org/abs/2611.22690.

A balanced 2k-vertex separator forces r disjoint crossing edges from any r vertices on the separator into an anticomplete outside shore containing at least r vertices.
-/

theorem balanced_cut_anticomplete_side_has_cross_matching
    (k r : ℕ) (hr : 1 ≤ r)
    (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (hsep : ∀ S P Q : Finset (Fin (4*k)), P.Nonempty → Q.Nonempty →
      Disjoint S P → Disjoint S Q → Disjoint P Q → S ∪ P ∪ Q = Finset.univ →
      (∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v) → 2*k ≤ S.card)
    (C H U : Finset (Fin (4*k))) (hcard : C.card = 2*k)
    (hCH : Disjoint C H) (hUC : U ⊆ C)
    (hanti : ∀ u ∈ H, ∀ v, v ∉ C → v ∉ H → ¬ G.Adj u v)
    (hrU : r ≤ U.card) (hrH : r ≤ H.card) :
    ∃ f g : Fin r → Fin (4*k), Function.Injective f ∧ Function.Injective g ∧
      (∀ i, f i ∈ U ∧ g i ∈ H ∧ G.Adj (f i) (g i)) := by
  classical
  obtain ⟨U0, hU0U, hU0card⟩ := Finset.exists_subset_card_eq hrU
  let choices : U0 → Finset (Fin (4*k)) := fun x => H.filter (G.Adj x.val)
  have hall : ∀ T : Finset U0, T.card ≤ (T.biUnion choices).card := by
    intro T
    by_contra hn
    have hlt : (T.biUnion choices).card < T.card := by omega
    let T' : Finset (Fin (4*k)) := T.image Subtype.val
    let N : Finset (Fin (4*k)) := T.biUnion choices
    have hTcard : T'.card = T.card := Finset.card_image_of_injective _ Subtype.val_injective
    have hTC : T' ⊆ C := by
      intro x hx
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
      exact hUC (hU0U u.property)
    have hNH : N ⊆ H := by
      intro x hx
      obtain ⟨u,hu,hx⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_filter.mp hx).1
    have hTn : T'.Nonempty := by
      apply Finset.card_pos.mp
      rw [hTcard]
      omega
    have hNr : N.card < H.card := by
      have ht : T.card ≤ r := by
        have hh := Finset.card_le_univ T
        simpa [hU0card] using hh
      have hnlt : N.card < T.card := by simpa [N] using hlt
      omega
    let S : Finset (Fin (4*k)) := (C \ T') ∪ N
    let P : Finset (Fin (4*k)) := H \ N
    let Q : Finset (Fin (4*k)) := Finset.univ \ (S ∪ P)
    have hP : P.Nonempty := by
      apply Finset.card_pos.mp
      have hnsub : N ⊆ H := hNH
      have hh := Finset.card_sdiff_add_card_eq_card hnsub
      dsimp [P]
      omega
    have hSP : Disjoint S P := by
      apply Finset.disjoint_left.mpr
      intro x hxS hxP
      have hp := Finset.mem_sdiff.mp hxP
      rcases Finset.mem_union.mp hxS with hx | hx
      · exact Finset.disjoint_left.mp hCH (Finset.mem_sdiff.mp hx).1 hp.1
      · exact hp.2 hx
    have hSQ : Disjoint S Q := by
      apply Finset.disjoint_left.mpr
      intro x hxS hxQ
      exact (Finset.mem_sdiff.mp hxQ).2 (Finset.mem_union_left P hxS)
    have hPQ : Disjoint P Q := by
      apply Finset.disjoint_left.mpr
      intro x hxP hxQ
      exact (Finset.mem_sdiff.mp hxQ).2 (Finset.mem_union_right S hxP)
    have hTQ : T' ⊆ Q := by
      intro x hx
      have hxC := hTC hx
      have hxH : x ∉ H := fun hh => Finset.disjoint_left.mp hCH hxC hh
      have hxN : x ∉ N := fun hh => hxH (hNH hh)
      have hxS : x ∉ S := by
        simp [S,hx,hxN]
      have hxP : x ∉ P := fun hh => hxH (Finset.mem_sdiff.mp hh).1
      simp [Q,hxS,hxP]
    have hQ : Q.Nonempty := hTn.mono hTQ
    have hcover : S ∪ P ∪ Q = Finset.univ := by
      ext x
      simp [Q]
    have hno : ∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v := by
      intro u hu v hv huv
      have huH := (Finset.mem_sdiff.mp hu).1
      have huN := (Finset.mem_sdiff.mp hu).2
      have hvS : v ∉ S := by
        intro hh
        exact Finset.disjoint_left.mp hSQ hh hv
      have hvP : v ∉ P := by
        intro hh
        exact Finset.disjoint_left.mp hPQ hh hv
      by_cases hvC : v ∈ C
      · have hvT : v ∈ T' := by
          by_contra hnT
          apply hvS
          exact Finset.mem_union_left N (Finset.mem_sdiff.mpr ⟨hvC,hnT⟩)
        obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hvT
        apply huN
        apply Finset.mem_biUnion.mpr
        exact ⟨w,hw,Finset.mem_filter.mpr ⟨huH,huv.symm⟩⟩
      · have hvH : v ∉ H := by
          intro hh
          by_cases hvN : v ∈ N
          · exact hvS (Finset.mem_union_right (C \ T') hvN)
          · exact hvP (Finset.mem_sdiff.mpr ⟨hh,hvN⟩)
        exact hanti u huH v hvC hvH huv
    have hScard : S.card < 2*k := by
      have hh := Finset.card_union_le (C \ T') N
      have ht := Finset.card_sdiff_add_card_eq_card hTC
      have hn' : N.card < T'.card := by simpa [hTcard] using hlt
      dsimp [S]
      omega
    have hsep' := hsep S P Q hP hQ hSP hSQ hPQ hcover hno
    omega
  obtain ⟨f,hfinj,hmem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' choices).mp hall
  let e : Fin r ≃ U0 := (Finset.equivFinOfCardEq hU0card).symm
  refine ⟨fun i => (e i).val, fun i => f (e i), ?_, ?_, ?_⟩
  · exact Subtype.val_injective.comp e.injective
  · exact hfinj.comp e.injective
  · intro i
    have hm := Finset.mem_filter.mp (hmem (e i))
    exact ⟨hU0U (e i).property, hm.1, hm.2⟩
