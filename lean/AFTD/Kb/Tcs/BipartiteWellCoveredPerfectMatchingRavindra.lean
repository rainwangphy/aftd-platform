import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# bipartite_well_covered_perfect_matching_ravindra

Topic: graphs   Node: beb4fdef8914

Provenance: helper lemma. step towards bipartite_well_covered_exists_perfect_matching_ravindra

In any finite connected well-covered bipartite graph G with at least 2 vertices, for any perfect matching M and any edge uv of M, every neighbor of u is adjacent to every neighbor of v.
-/

/-- Ravindra's neighborhood property: in a well-covered bipartite graph, any perfect matching has complete bipartite neighborhoods. -/
theorem bipartite_well_covered_perfect_matching_ravindra {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hconn : G.Connected) (hbip : G.IsBipartite)
    (hcard : 2 ≤ Fintype.card V) (hwc : simple_graph_is_well_covered G)
    (M : SimpleGraph.Subgraph G) (hM : M.IsPerfectMatching)
    (u v : V) (huv : M.Adj u v) (x y : V) (hx : G.Adj u x) (hy : G.Adj v y) :
    G.Adj x y := by
  classical
  by_contra hxy
  have hne : ∀ z : V, ∃ w, G.Adj z w := by
    intro z
    obtain ⟨w, hw⟩ : ∃ w, w ≠ z := by
      by_contra h
      push Not at h
      have : Fintype.card V ≤ 1 := Fintype.card_le_one_iff.mpr fun a b => by rw [h a, h b]
      omega
    have hr : G.Reachable z w := hconn.preconnected z w
    exact hr.elim fun p => by
      cases p with
      | nil => exact absurd rfl hw
      | cons h _ => exact ⟨_, h⟩
  obtain ⟨C⟩ := hbip
  have htwo : ∀ c : Fin 2, c = 0 ∨ c = 1 := fun c => by fin_cases c <;> simp
  set A : Set V := C.colorClass 0 with hAdef
  set B : Set V := C.colorClass 1 with hBdef
  have hAind : G.IsIndepSet A := C.isIndepSet_colorClass 0
  have hBind : G.IsIndepSet B := C.isIndepSet_colorClass 1
  have hunion : A ∪ B = Set.univ := by
    ext z
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    rcases htwo (C z) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hmem : ∀ z : V, z ∈ A ∪ B := fun z => by rw [hunion]; trivial
  have hAmax : Maximal G.IsIndepSet A := by
    refine ⟨hAind, ?_⟩
    intro t ht hAt z hz
    by_contra hzA
    have hzB : z ∈ B := by
      have h := hmem z
      rw [Set.mem_union] at h
      exact h.resolve_left hzA
    obtain ⟨w, hw⟩ := hne z
    have hwB : w ∉ B := fun hwB' => hBind hzB hwB' hw.ne hw
    have hwA : w ∈ A := by
      have h := hmem w
      rw [Set.mem_union] at h
      exact h.resolve_right hwB
    exact ht (hAt hwA) hz hw.ne.symm hw.symm
  have hBmax : Maximal G.IsIndepSet B := by
    refine ⟨hBind, ?_⟩
    intro t ht hBt z hz
    by_contra hzB
    have hzA : z ∈ A := by
      have h := hmem z
      rw [Set.mem_union] at h
      exact h.resolve_right hzB
    obtain ⟨w, hw⟩ := hne z
    have hwA : w ∉ A := fun hwA' => hAind hzA hwA' hw.ne hw
    have hwB : w ∈ B := by
      have h := hmem w
      rw [Set.mem_union] at h
      exact h.resolve_left hwA
    exact ht (hBt hwB) hz hw.ne.symm hw.symm
  let AF : Finset V := Finset.univ.filter (fun z => C z = 0)
  let BF : Finset V := Finset.univ.filter (fun z => C z = 1)
  have hAFcoe : (AF : Set V) = A := by
    ext z; simp [AF, A, SimpleGraph.Coloring.colorClass]
  have hBFcoe : (BF : Set V) = B := by
    ext z; simp [BF, B, SimpleGraph.Coloring.colorClass]
  have hAFmax : Maximal (fun s : Finset V => G.IsIndepSet (s : Set V)) AF := by
    refine ⟨?_, ?_⟩
    · show G.IsIndepSet (AF : Set V)
      rw [hAFcoe]; exact hAind
    · intro t ht hsub
      have h1 : A ⊆ (t : Set V) := by
        rw [← hAFcoe]
        exact Finset.coe_subset.mpr hsub
      have h2 : (t : Set V) ⊆ A := hAmax.2 ht h1
      intro z hz
      exact Finset.mem_coe.mp (hAFcoe ▸ h2 hz)
  have hBFmax : Maximal (fun s : Finset V => G.IsIndepSet (s : Set V)) BF := by
    refine ⟨?_, ?_⟩
    · show G.IsIndepSet (BF : Set V)
      rw [hBFcoe]; exact hBind
    · intro t ht hsub
      have h1 : B ⊆ (t : Set V) := by
        rw [← hBFcoe]
        exact Finset.coe_subset.mpr hsub
      have h2 : (t : Set V) ⊆ B := hBmax.2 ht h1
      intro z hz
      exact Finset.mem_coe.mp (hBFcoe ▸ h2 hz)
  have hAFBFdisj : Disjoint AF BF := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    simp only [AF, BF, Finset.mem_filter, Finset.mem_univ, true_and] at hz hz'
    exact absurd (hz.symm.trans hz') (by decide)
  have hAFBFun : AF ∪ BF = Finset.univ := by
    refine Finset.eq_univ_iff_forall.mpr ?_
    intro z
    rw [Finset.mem_union]
    simp only [AF, BF, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases htwo (C z) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hVcard : Fintype.card V = AF.card + BF.card := by
    have h := Finset.card_union_of_disjoint hAFBFdisj
    rw [hAFBFun, Finset.card_univ] at h
    exact h
  have hxyind : G.IsIndepSet ({x, y} : Set V) := by
    intro a ha b hb hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact hxy
    · exact fun h => hxy h.symm
    · exact absurd rfl hab
  let fam : Finset (Finset V) :=
    Finset.univ.filter (fun t : Finset V => x ∈ t ∧ y ∈ t ∧ G.IsIndepSet (t : Set V))
  have hfamne : fam.Nonempty := by
    refine ⟨{x, y}, ?_⟩
    simp only [fam, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by simp, by simp, by simpa using hxyind⟩
  obtain ⟨s, hsmax⟩ := Finset.exists_maximal hfamne
  have hsmem : x ∈ s ∧ y ∈ s ∧ G.IsIndepSet (s : Set V) := by
    have h := hsmax.1
    simp only [fam, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h
  have hsFmax : Maximal (fun t : Finset V => G.IsIndepSet (t : Set V)) s := by
    refine ⟨hsmem.2.2, ?_⟩
    intro t ht hst
    have ht_fam : t ∈ fam := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ t, ?_⟩
      exact ⟨hst hsmem.1, hst hsmem.2.1, ht⟩
    exact hsmax.2 ht_fam hst
  have hsA : s.card = AF.card := hwc s AF hsFmax hAFmax
  have hAB : AF.card = BF.card := hwc AF BF hAFmax hBFmax
  have hu_not : u ∉ s := by
    intro hu
    exact hsmem.2.2 hu hsmem.1 hx.ne hx
  have hv_not : v ∉ s := by
    intro hv
    exact hsmem.2.2 hv hsmem.2.1 hy.ne hy
  have hspan : ∀ z : V, z ∈ M.verts := hM.2
  have hmatch : ∀ z : V, ∃! w, M.Adj z w := fun z => hM.1 (hspan z)
  let f : V → V := fun z => (hmatch z).choose
  have hfadj : ∀ z, M.Adj z (f z) := fun z => (hmatch z).choose_spec.1
  have hfuniq : ∀ z w, M.Adj z w → w = f z := fun z w h => (hmatch z).choose_spec.2 w h
  have hfsym : ∀ z, f (f z) = z := by
    intro z
    exact (hfuniq (f z) z (M.symm.symm z (f z) (hfadj z))).symm
  have hfinj : Function.Injective f := by
    intro a b hab
    calc a = f (f a) := (hfsym a).symm
      _ = f (f b) := by rw [hab]
      _ = b := hfsym b
  have hfne : ∀ z, f z ≠ z := by
    intro z h
    have h1 : M.Adj z (f z) := hfadj z
    rw [h] at h1
    exact G.irrefl (M.adj_sub h1)
  have hfG : ∀ z, G.Adj z (f z) := fun z => M.adj_sub (hfadj z)
  have hfu : f u = v := (hfuniq u v huv).symm
  have hfv : f v = u := (hfuniq v u (M.symm.symm u v huv)).symm
  have hdisj_img : Disjoint s (s.image f) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp ha'
    have hne' : b ≠ a := by
      rintro rfl
      exact hfne b hba
    have hAdj : G.Adj b a := by rw [← hba]; exact hfG b
    exact (hsmem.2.2 hb ha hne') hAdj
  have hcard_img : (s.image f).card = s.card := Finset.card_image_of_injective s hfinj
  have hcard_union : (s ∪ s.image f).card = s.card + s.card := by
    rw [Finset.card_union_of_disjoint hdisj_img, hcard_img]
  have hu_not_img : u ∉ s.image f := by
    intro hu_img
    obtain ⟨a, ha, hfa⟩ := Finset.mem_image.mp hu_img
    have hav : a = v := by
      have h1 : f (f a) = f u := congrArg f hfa
      rw [hfsym a, hfu] at h1
      exact h1
    exact hv_not (hav ▸ ha)
  have hv_not_img : v ∉ s.image f := by
    intro hv_img
    obtain ⟨a, ha, hfa⟩ := Finset.mem_image.mp hv_img
    have hau : a = u := by
      have h1 : f (f a) = f v := congrArg f hfa
      rw [hfsym a, hfv] at h1
      exact h1
    exact hu_not (hau ▸ ha)
  have hdisj_uv : Disjoint (s ∪ s.image f) ({u, v} : Finset V) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    simp only [Finset.mem_union] at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha'
    rcases ha with ha | ha <;> rcases ha' with rfl | rfl
    · exact hu_not ha
    · exact hv_not ha
    · exact hu_not_img ha
    · exact hv_not_img ha
  have hupper : s.card + s.card + 2 ≤ Fintype.card V := by
    have h1 : ((s ∪ s.image f) ∪ ({u, v} : Finset V)).card
        = (s ∪ s.image f).card + ({u, v} : Finset V).card :=
      Finset.card_union_of_disjoint hdisj_uv
    have h2 : ((s ∪ s.image f) ∪ ({u, v} : Finset V)) ⊆ Finset.univ := Finset.subset_univ _
    have h3 : ({u, v} : Finset V).card = 2 := Finset.card_pair (M.adj_sub huv).ne
    have h4 : ((s ∪ s.image f) ∪ ({u, v} : Finset V)).card ≤ Fintype.card V := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card h2
    omega
  omega
