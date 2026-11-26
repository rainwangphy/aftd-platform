import AFTD.Prelude
import AFTD.Kb.Tcs.BalancedCutAnticompleteSideHasCrossMatching
import AFTD.Kb.Tcs.IndexedDisjointCrossEdgesFormMatching
import AFTD.Kb.Tcs.ExtendibleGraphMatchableDeletionInheritsExtendibility
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable

/-!
# balanced_cut_extend_internal_matching

Topic: graphs   Node: 857cad3ea7ca

Provenance: helper lemma. Balanced-cut matching construction for OP-1957; https://arxiv.org/abs/2611.22690.

The separator cross-matching extends a balanced-side matching of k−r edges to a k-matching, leaving exactly r vertices on that side uncovered.
-/

theorem balanced_cut_extend_internal_matching
    (k r : ℕ) (hr : 1 ≤ r)
    (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (hsep : ∀ S P Q : Finset (Fin (4*k)), P.Nonempty → Q.Nonempty →
      Disjoint S P → Disjoint S Q → Disjoint P Q → S ∪ P ∪ Q = Finset.univ →
      (∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v) → 2*k ≤ S.card)
    (C H : Finset (Fin (4*k))) (hcard : C.card = 2*k)
    (hCH : Disjoint C H)
    (hanti : ∀ u ∈ H, ∀ v, v ∉ C → v ∉ H → ¬ G.Adj u v)
    (hrH : r ≤ H.card)
    (M : G.Subgraph) (hM : M.IsMatching) (hMC : M.verts ⊆ (C : Set (Fin (4*k))))
    (hm : M.edgeSet.ncard+r = k) :
    ∃ T : G.Subgraph, T.IsMatching ∧ T.edgeSet.ncard = k ∧ M ≤ T ∧
      T.verts ⊆ (C ∪ H : Finset (Fin (4*k))) ∧
      ((C : Set (Fin (4*k))) \ T.verts).ncard = r := by
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
  have hrU : r ≤ U.card := by omega
  obtain ⟨f,g,hf,hg,hfg⟩ :=
    balanced_cut_anticomplete_side_has_cross_matching k r hr G hsep C H U
      hcard hCH hUC hanti hrU hrH
  have hfgdis : ∀ i j, f i ≠ g j := by
    intro i j he
    have hc := hUC (hfg i).1
    have hh := (hfg j).2.1
    exact Finset.disjoint_left.mp hCH hc (he.symm ▸ hh)
  obtain ⟨N,hN,hNcard,hNverts⟩ :=
    indexed_disjoint_cross_edges_form_matching G r f g hf hg hfgdis (fun i => (hfg i).2.2)
  have hMN : Disjoint M.verts N.verts := by
    apply Set.disjoint_left.mpr
    intro v hvM hvN
    rw [hNverts] at hvN
    rcases hvN with ⟨i,hi⟩ | ⟨i,hi⟩
    · have hu := (hfg i).1
      have hn : f i ∉ D := (Finset.mem_sdiff.mp hu).2
      apply hn
      simpa [D,hi] using hvM
    · have hc := hMC hvM
      have hh := (hfg i).2.1
      exact Finset.disjoint_left.mp hCH hc (hi ▸ hh)
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
  have hTsub : (M ⊔ N).verts ⊆ (C ∪ H : Finset (Fin (4*k))) := by
    intro v hv
    change v ∈ M.verts ∪ N.verts at hv
    rcases hv with hv | hv
    · exact Finset.mem_union_left H (hMC hv)
    · rw [hNverts] at hv
      rcases hv with ⟨i,rfl⟩ | ⟨i,rfl⟩
      · exact Finset.mem_union_left H (hUC (hfg i).1)
      · exact Finset.mem_union_right C (hfg i).2.1
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
        · exact Finset.disjoint_left.mp hCH hvC (hi ▸ (hfg i).2.1)
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
  refine ⟨M ⊔ N,hT.1,hTk,le_sup_left,hTsub,hremain'⟩
