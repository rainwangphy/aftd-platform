import AFTD.Prelude
import AFTD.Kb.Tcs.OddComponentBoundAfterEvenDeletions
import AFTD.Kb.Tcs.IndexedDisjointCrossEdgesFormMatching
import AFTD.Kb.Tcs.ExtendibleGraphMatchableDeletionInheritsExtendibility
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable
import AFTD.Kb.Tcs.InducedComponentAmbientVertexProperties

/-!
# extendible_balanced_cut_odd_bound_of_parity_cross_matching

Topic: graphs   Node: 7a75195290f4

Provenance: helper lemma. Balanced-cut reduction for OP-1957; https://arxiv.org/abs/2611.22690.

For the stated order-4k extendible graph and balanced-side matching with deficiency r, the opposite side has at most r+1 odd components whenever the displayed parity-controlled crossing-matching condition holds.
-/

theorem extendible_balanced_cut_odd_bound_of_parity_cross_matching
    (k r : ℕ) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (hext : is_k_extendable G k)
    (C : Finset (Fin (4*k))) (hcard : C.card = 2*k)
    (M : G.Subgraph) (hM : M.IsMatching) (hMC : M.verts ⊆ (C : Set (Fin (4*k))))
    (hm : M.edgeSet.ncard+r = k)
    (hcross : ∀ U : Finset (Fin (4*k)), U ⊆ C → U.card = 2*r →
      ∃ f g : Fin r → Fin (4*k), Function.Injective f ∧ Function.Injective g ∧
        (∀ i, f i ∈ U ∧ g i ∉ C ∧ G.Adj (f i) (g i)) ∧
        ∃ B : Finset (G.induce {v | v ∉ C}).ConnectedComponent, B.card ≤ 1 ∧
          ∀ i ∈ (G.induce {v | v ∉ C}).oddComponents.toFinset, i ∉ B →
            Even ((in1206_component_vertices G {v | v ∉ C} i) ∩
              ((Finset.univ : Finset (Fin r)).image g)).card) :
    (G.induce {v | v ∉ C}).oddComponents.ncard ≤ r+1 := by
  set_option maxHeartbeats 4000000 in
    classical
    let D : Finset (Fin (4*k)) := M.verts.toFinset
    let U : Finset (Fin (4*k)) := C \ D
    have hDC : D ⊆ C := by
      intro v hv
      exact hMC (by simpa [D] using hv)
    have hDcard : D.card + 2*r = 2*k := by
      have hh := in1076_matching_twice_card hM
      have hD : D.card = M.verts.ncard := by
        dsimp [D]
        exact (Set.ncard_eq_toFinset_card' M.verts).symm
      rw [hD] at *
      omega
    have hUcard : U.card = 2*r := by
      have hh := Finset.card_sdiff_add_card_eq_card hDC
      dsimp [U]
      omega
    have hUC : U ⊆ C := Finset.sdiff_subset
    obtain ⟨f,g,hf,hg,hfg,B,hB,hpar⟩ := hcross U hUC hUcard
    have hfgdis : ∀ i j, f i ≠ g j := by
      intro i j he
      have hc := hUC (hfg i).1
      exact (hfg j).2.1 (he ▸ hc)
    obtain ⟨N,hN,hNcard,hNverts⟩ :=
      indexed_disjoint_cross_edges_form_matching G r f g hf hg hfgdis (fun i => (hfg i).2.2)
    have hMN : Disjoint M.verts N.verts := by
      apply Set.disjoint_left.mpr
      intro v hvM hvN
      rw [hNverts] at hvN
      rcases hvN with ⟨i,hi⟩ | ⟨i,hi⟩
      · have hn : f i ∉ D := (Finset.mem_sdiff.mp (hfg i).1).2
        apply hn
        simpa [D,hi] using hvM
      · have hc := hMC hvM
        exact (hfg i).2.1 (hi ▸ hc)
    have hT := extendible_graph_matchable_deletion_inherits_extendibility_sup_ncard M N hM hN hMN
    have hTk : (M ⊔ N).edgeSet.ncard = k := by rw [hT.2,hNcard]; omega
    let A : Finset (Fin (4*k)) := Finset.univ.image f
    have hAcard : A.card = r := by
      rw [Finset.card_image_of_injective _ hf]
      simp
    have hAC : A ⊆ C := by
      intro v hv
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
      exact hUC (hfg i).1
    have hDA : Disjoint D A := by
      apply Finset.disjoint_left.mpr
      intro v hvD hvA
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hvA
      exact (Finset.mem_sdiff.mp (hfg i).1).2 hvD
    have hfilter : C.filter (fun v => v ∉ (M ⊔ N).verts) = C \ (D ∪ A) := by
      ext v
      simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_union]
      constructor
      · rintro ⟨hvC,hvT⟩
        refine ⟨hvC,?_⟩
        rintro (hvD | hvA)
        · apply hvT
          change v ∈ M.verts ∪ N.verts
          exact Or.inl (by simpa [D] using hvD)
        · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hvA
          apply hvT
          change f i ∈ M.verts ∪ N.verts
          right
          rw [hNverts]
          exact Or.inl ⟨i,rfl⟩
      · rintro ⟨hvC,hvnot⟩
        refine ⟨hvC,?_⟩
        intro hvT
        change v ∈ M.verts ∪ N.verts at hvT
        rcases hvT with hvM | hvN
        · exact hvnot (Or.inl (by simpa [D] using hvM))
        · rw [hNverts] at hvN
          rcases hvN with ⟨i,hi⟩ | ⟨i,hi⟩
          · apply hvnot
            right
            exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩
          · exact (hfg i).2.1 (hi ▸ hvC)
    have hremain : (C.filter (fun v => v ∉ (M ⊔ N).verts)).card = r := by
      rw [hfilter]
      have hsub : D ∪ A ⊆ C := Finset.union_subset hDC hAC
      have hh := Finset.card_sdiff_add_card_eq_card hsub
      rw [Finset.card_union_of_disjoint hDA,hAcard] at hh
      omega
    have hremain' : ((C : Set (Fin (4*k))) \ (M ⊔ N).verts).ncard = r := by
      have heq : (C : Set (Fin (4*k))) \ (M ⊔ N).verts =
          (C.filter (fun v => v ∉ (M ⊔ N).verts) : Finset (Fin (4*k))) := by
        ext v
        simp
      rw [heq,Set.ncard_coe_finset]
      exact hremain
    have hnewpar : ∀ i ∈ (G.induce {v | v ∉ C}).oddComponents.toFinset, i ∉ B →
        Even ((in1206_component_vertices G {v | v ∉ C} i) ∩ (M ⊔ N).verts.toFinset).card := by
      intro i hi hiB
      have heq : (in1206_component_vertices G {v | v ∉ C} i) ∩ (M ⊔ N).verts.toFinset =
          (in1206_component_vertices G {v | v ∉ C} i) ∩ (Finset.univ.image g) := by
        ext v
        simp only [Finset.mem_inter, Set.mem_toFinset, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hvF,hvT⟩
          refine ⟨hvF,?_⟩
          have hvR := (induced_component_ambient_vertex_properties G {v | v ∉ C} i i).1 hvF
          change v ∈ M.verts ∪ N.verts at hvT
          rcases hvT with hvM | hvN
          · exact False.elim (hvR (hMC hvM))
          · rw [hNverts] at hvN
            rcases hvN with ⟨j,hj⟩ | ⟨j,hj⟩
            · exact False.elim (hvR (hj ▸ hUC (hfg j).1))
            · exact ⟨j,hj⟩
        · rintro ⟨hvF,⟨j,hj⟩⟩
          refine ⟨hvF,?_⟩
          change v ∈ M.verts ∪ N.verts
          right
          rw [hNverts]
          exact Or.inr ⟨j,hj⟩
      rw [heq]
      exact hpar i hi hiB
    obtain ⟨P,hP,hTP⟩ := hext.2.2 (M ⊔ N) hT.1 hTk
    exact odd_component_bound_after_even_deletions k r G C P (M ⊔ N) hP hT.1 hTP B hB hnewpar hremain'
