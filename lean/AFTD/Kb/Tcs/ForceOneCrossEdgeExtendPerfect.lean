import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.BalancedCutSeparatorImpliesMinDegree
import AFTD.Kb.Tcs.HighMinDegreeMatchingExtendsToSize
import AFTD.Kb.Tcs.IndexedDisjointCrossEdgesFormMatching
import AFTD.Kb.Tcs.ExtendibleGraphMatchableDeletionInheritsExtendibility
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable

/-!
# force_one_cross_edge_extend_perfect

Topic: graphs   Node: ca5d086cd915

Provenance: helper lemma. Balanced-cut k=7 reduction for OP-1957; https://arxiv.org/abs/2611.22690.

In the displayed extendible graph, a crossing edge from an uncovered vertex to the opposite side can be forced into a perfect matching along with the original internal matching.
-/

theorem force_one_cross_edge_extend_perfect
    (k r : ℕ) (hr : 1 ≤ r) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (hext : is_k_extendable G k)
    (hsep : ∀ S P Q : Finset (Fin (4*k)), P.Nonempty → Q.Nonempty →
      Disjoint S P → Disjoint S Q → Disjoint P Q → S ∪ P ∪ Q = Finset.univ →
      (∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v) → 2*k ≤ S.card)
    (C : Finset (Fin (4*k))) (hcard : C.card = 2*k)
    (M : G.Subgraph) (hM : M.IsMatching) (hMC : M.verts ⊆ (C : Set (Fin (4*k))))
    (hm : M.edgeSet.ncard+r=k) (x u : Fin (4*k)) (hxC : x ∉ C)
    (huC : u ∈ C) (huM : u ∉ M.verts) (hux : G.Adj u x) :
    ∃ P T : G.Subgraph, P.IsPerfectMatching ∧ T.IsMatching ∧ T ≤ P ∧
      x ∈ T.verts ∧ T.verts ⊆ ((C ∪ {x} : Finset (Fin (4*k))) : Set (Fin (4*k))) ∧
      ((C : Set (Fin (4*k))) \ T.verts).ncard = 2*r-1 := by
  set_option maxHeartbeats 4000000 in
    classical
    let X : Finset (Fin (4*k)) := {x}
    have hCX : Disjoint C X := by simpa [X] using hxC
    have hX : X.card ≤ r := by simpa [X] using hr
    have hexpose : ∃ f : X → Fin (4*k), Function.Injective f ∧
        ∀ y : X, f y ∈ C ∧ f y ∉ M.verts ∧ G.Adj (f y) y.val := by
      refine ⟨fun _ => u,?_,?_⟩
      · intro a b h
        apply Subtype.ext
        have ha : a.val=x := Finset.mem_singleton.mp (show a.val ∈ ({x} : Finset (Fin (4*k))) from a.property)
        have hb : b.val=x := Finset.mem_singleton.mp (show b.val ∈ ({x} : Finset (Fin (4*k))) from b.property)
        exact ha.trans hb.symm
      · intro y
        have hy : y.val=x := Finset.mem_singleton.mp (show y.val ∈ ({x} : Finset (Fin (4*k))) from y.property)
        simpa [hy] using ⟨huC,huM,hux⟩
    have hk : 1 ≤ k := by
      have h := hext.1
      simp only [Fintype.card_fin] at h
      omega
    have hd := balanced_cut_separator_implies_min_degree k hk G hsep
    obtain ⟨f,hf,hfprop⟩ := hexpose
    let e : Fin X.card ≃ X := (Finset.equivFinOfCardEq rfl).symm
    let a : Fin X.card → Fin (4*k) := fun i => f (e i)
    let b : Fin X.card → Fin (4*k) := fun i => (e i).val
    have ha : Function.Injective a := hf.comp e.injective
    have hb : Function.Injective b := Subtype.val_injective.comp e.injective
    have habdis : ∀ i j, a i ≠ b j := by
      intro i j he
      have hc := (hfprop (e i)).1
      have hx := (e j).property
      have he' : f (e i) = (e j).val := he
      have hx' : f (e i) ∈ X := by simpa [he'] using hx
      exact Finset.disjoint_left.mp hCX hc hx'
    obtain ⟨E,hE,hEcard,hEverts⟩ := indexed_disjoint_cross_edges_form_matching G X.card a b ha hb habdis (by intro i; exact (hfprop (e i)).2.2)
    have hME : Disjoint M.verts E.verts := by
      apply Set.disjoint_left.mpr
      intro v hvM hvE
      rw [hEverts] at hvE
      rcases hvE with ⟨i,hi⟩ | ⟨i,hi⟩
      · have hi' : f (e i) = v := hi
        have hbad : f (e i) ∈ M.verts := by rw [hi']; exact hvM
        exact (hfprop (e i)).2.1 hbad
      · exact Finset.disjoint_left.mp hCX (hMC hvM) (hi ▸ (e i).property)
    have hT := extendible_graph_matchable_deletion_inherits_extendibility_sup_ncard M E hM hE hME
    have hTk : (M ⊔ E).edgeSet.ncard ≤ k := by rw [hT.2,hEcard]; omega
    obtain ⟨N,hN,hTN,hNk⟩ := high_min_degree_matching_extends_to_size G k hext.1 hd (M ⊔ E) hT.1 hTk
    obtain ⟨P,hP,hNP⟩ := hext.2.2 N hN hNk
    have hTP : M ⊔ E ≤ P := le_trans hTN hNP
    have hTX : (X : Set (Fin (4*k))) ⊆ (M ⊔ E).verts := by
      intro x hx
      change x ∈ M.verts ∪ E.verts
      right
      rw [hEverts]
      right
      let i := e.symm ⟨x,hx⟩
      refine ⟨i,?_⟩
      change (e i).val = x
      simp [i]
    have hTsub : (M ⊔ E).verts ⊆ ((C ∪ X : Finset (Fin (4*k))) : Set (Fin (4*k))) := by
      intro v hv
      change v ∈ M.verts ∪ E.verts at hv
      rcases hv with hvM | hvE
      · exact Finset.mem_union_left X (hMC hvM)
      · rw [hEverts] at hvE
        rcases hvE with ⟨i,hi⟩ | ⟨i,hi⟩
        · exact Finset.mem_union_left X (hi ▸ (hfprop (e i)).1)
        · exact Finset.mem_union_right C (hi ▸ (e i).property)
    let D : Finset (Fin (4*k)) := M.verts.toFinset
    let A : Finset (Fin (4*k)) := Finset.univ.image a
    have hDcard : D.card+2*r=2*k := by
      have hh := in1076_matching_twice_card hM
      have hD : D.card = M.verts.ncard := by
        dsimp [D]
        exact (Set.ncard_eq_toFinset_card' M.verts).symm
      rw [hD] at *
      omega
    have hAcard : A.card=X.card := by
      rw [Finset.card_image_of_injective _ ha]
      simp
    have hDC : D ⊆ C := by
      intro v hv
      exact hMC (by simpa [D] using hv)
    have hAC : A ⊆ C := by
      intro v hv
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
      exact (hfprop (e i)).1
    have hDA : Disjoint D A := by
      apply Finset.disjoint_left.mpr
      intro v hvD hvA
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hvA
      exact (hfprop (e i)).2.1 (by simpa [D] using hvD)
    have hfilter : C.filter (fun v => v ∉ (M ⊔ E).verts) = C \ (D ∪ A) := by
      ext v
      simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_union]
      constructor
      · rintro ⟨hvC,hvT⟩
        refine ⟨hvC,?_⟩
        rintro (hvD | hvA)
        · apply hvT
          change v ∈ M.verts ∪ E.verts
          exact Or.inl (by simpa [D] using hvD)
        · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hvA
          apply hvT
          change a i ∈ M.verts ∪ E.verts
          right
          rw [hEverts]
          exact Or.inl ⟨i,rfl⟩
      · rintro ⟨hvC,hvnot⟩
        refine ⟨hvC,?_⟩
        intro hvT
        change v ∈ M.verts ∪ E.verts at hvT
        rcases hvT with hvM | hvE
        · exact hvnot (Or.inl (by simpa [D] using hvM))
        · rw [hEverts] at hvE
          rcases hvE with ⟨i,hi⟩ | ⟨i,hi⟩
          · apply hvnot
            right
            exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩
          · exact Finset.disjoint_left.mp hCX hvC (hi ▸ (e i).property)
    have hremain : (C.filter (fun v => v ∉ (M ⊔ E).verts)).card = 2*r-X.card := by
      rw [hfilter]
      have hsub : D ∪ A ⊆ C := Finset.union_subset hDC hAC
      have hh := Finset.card_sdiff_add_card_eq_card hsub
      rw [Finset.card_union_of_disjoint hDA,hAcard] at hh
      omega
    have hremain' : ((C : Set (Fin (4*k))) \ (M ⊔ E).verts).ncard = 2*r-X.card := by
      have heq : (C : Set (Fin (4*k))) \ (M ⊔ E).verts =
          (C.filter (fun v => v ∉ (M ⊔ E).verts) : Finset (Fin (4*k))) := by
        ext v
        simp
      rw [heq,Set.ncard_coe_finset]
      exact hremain
    refine ⟨P,M ⊔ E,hP,hT.1,hTP,?_,?_,?_⟩
    · exact hTX (by simp [X])
    · simpa [X] using hTsub
    · simpa [X] using hremain'
