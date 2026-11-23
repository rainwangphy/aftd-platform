import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# boundary_saturated_block_cross_edge_residual_reachable

Topic: graphs   Node: 9993db7254e0

Provenance: helper lemma. OP-1957; bridge exclusion for the one-three-vertex-block boundary route, session IN-1122.

Under the displayed four-block, saturation, degree, and 2k-separator hypotheses, if A has at least three vertices and the opposite block C has at most k vertices, every 2k-vertex residual containing a cross edge from A to C has an alternate path between its endpoints.
-/

theorem boundary_saturated_block_cross_edge_residual_reachable
    (k : ℕ) (hk : 4 ≤ k) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hsizeAB : A.card+B.card=2*k) (hsizeCD : C.card+D.card=2*k)
    (hA : 3 ≤ A.card) (hC : C.card ≤ k)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ c ∈ C, ∀ d ∈ D, ¬ G.Adj c d)
    (hAsat : ∀ a ∈ A, ∀ w ∈ A ∪ C ∪ D, a ≠ w → G.Adj a w)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (hsep : ∀ X U V : Finset (Fin (4*k)), U.Nonempty → V.Nonempty →
      Disjoint X U → Disjoint X V → Disjoint U V → X ∪ U ∪ V = Finset.univ →
      (∀ u ∈ U, ∀ v ∈ V, ¬ G.Adj u v) → 2*k ≤ X.card)
    (R : Finset (Fin (4*k))) (hR : R.card = 2*k)
    (x y : Fin (4*k)) (hx : x ∈ A) (hy : y ∈ C) (hxy : G.Adj x y)
    (hxR : x ∈ R) (hyR : y ∈ R) :
    ((G.induce {a | a ∈ R}).deleteEdges {s(⟨x,hxR⟩,⟨y,hyR⟩)}).Reachable ⟨x,hxR⟩ ⟨y,hyR⟩ := by
  classical
  set H := (G.induce {a | a ∈ R}).deleteEdges {s(⟨x,hxR⟩,⟨y,hyR⟩)} with hH
  by_contra hnot
  -- S: vertices of R reachable from x in the residual
  set S : Finset (Fin (4*k)) :=
    Finset.univ.filter (fun v => ∃ h : v ∈ R, H.Reachable ⟨x,hxR⟩ ⟨v,h⟩) with hS
  have hxS : x ∈ S := by
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hxR, SimpleGraph.Reachable.refl _⟩
  have hSR : ∀ v ∈ S, v ∈ R := by
    intro v hv
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    exact hv.1
  have hyS : y ∉ S := by
    intro h
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at h
    obtain ⟨_, hr⟩ := h
    exact hnot hr
  have hxy_ne : x ≠ y := hxy.ne
  -- key propagation lemma
  have hstep : ∀ u ∈ S, ∀ w ∈ R, G.Adj u w → ¬ (u = x ∧ w = y) → ¬ (u = y ∧ w = x) → w ∈ S := by
    intro u hu w hw hadj h1 h2
    have huR := hSR u hu
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    obtain ⟨huR', hr⟩ := hu
    refine ⟨hw, hr.trans (SimpleGraph.Adj.reachable ?_)⟩
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨by simpa using hadj, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
      Subtype.mk.injEq]
    tauto
  -- A ∩ R = {x}
  have hAR : ∀ a ∈ A, a ∈ R → a = x := by
    intro a ha haR
    by_contra hax
    have hay : a ≠ y := fun h => Finset.disjoint_left.mp hAC ha (h ▸ hy)
    have haS : a ∈ S := hstep x hxS a haR (hAsat x hx a (by simp [ha]) (Ne.symm hax))
      (fun h => hay h.2) (fun h => hxy_ne h.1)
    exact hyS (hstep a haS y hyR (hAsat a ha y (by simp [hy]) hay) (fun h => hax h.1)
      (fun h => hay h.1))
  -- vertices of R outside S, other than y, lie in B
  have hWB : ∀ w ∈ R, w ∉ S → w ≠ y → w ∈ B := by
    intro w hwR hwS hwy
    have hwx : w ≠ x := fun h => hwS (h ▸ hxS)
    have hw : w ∈ A ∪ B ∪ C ∪ D := by rw [hcover]; exact Finset.mem_univ _
    simp only [Finset.mem_union] at hw
    rcases hw with ((hwA | hwB) | hwC) | hwD
    · exact absurd (hAR w hwA hwR) hwx
    · exact hwB
    · exact absurd (hstep x hxS w hwR (hAsat x hx w (by simp [hwC]) (Ne.symm hwx))
        (fun h => hwy h.2) (fun h => hxy_ne h.1)) hwS
    · exact absurd (hstep x hxS w hwR (hAsat x hx w (by simp [hwD]) (Ne.symm hwx))
        (fun h => hwy h.2) (fun h => hxy_ne h.1)) hwS
  -- y has a neighbour w ∈ R with w ≠ x
  obtain ⟨w, hwN, hwR, hwx⟩ : ∃ w ∈ G.neighborFinset y, w ∈ R ∧ w ≠ x := by
    by_contra hno
    push Not at hno
    have hsub : G.neighborFinset y ⊆ insert x (Finset.univ \ R) := by
      intro w hw
      by_cases hwR : w ∈ R
      · exact Finset.mem_insert.mpr (Or.inl (hno w hw hwR))
      · exact Finset.mem_insert_of_mem (by simp [hwR])
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le x (Finset.univ \ R)
    have h3 : (Finset.univ \ R).card = 2*k := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ R), Finset.card_univ, Fintype.card_fin, hR]
      omega
    have := hdegree y
    omega
  have hyw : G.Adj y w := by simpa using hwN
  have hwy : w ≠ y := fun h => G.irrefl (h ▸ hyw)
  have hwS : w ∉ S := by
    intro h
    exact hyS (hstep w h y hyR hyw.symm (fun h' => hwx h'.1) (fun h' => hwy h'.1))
  -- the separator
  set X : Finset (Fin (4*k)) := insert y ((Finset.univ \ R) \ A) with hX
  set U : Finset (Fin (4*k)) := S ∪ (A \ R) with hU
  set V : Finset (Fin (4*k)) := (R \ S).erase y with hV
  have hUne : U.Nonempty := ⟨x, by simp [hU, hxS]⟩
  have hwV : w ∈ V := by simp [hV, hwR, hwS, hwy]
  have hVne : V.Nonempty := ⟨w, hwV⟩
  have hXU : Disjoint X U := by
    rw [Finset.disjoint_left]
    intro v hvX hvU
    simp only [hX, hU, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union] at hvX hvU
    rcases hvX with rfl | ⟨hvR, hvA⟩
    · rcases hvU with h | ⟨h, _⟩
      · exact hyS h
      · exact Finset.disjoint_left.mp hAC h hy
    · rcases hvU with h | ⟨h, _⟩
      · exact hvR (hSR v h)
      · exact hvA h
  have hXV : Disjoint X V := by
    rw [Finset.disjoint_left]
    intro v hvX hvV
    simp only [hX, hV, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_erase] at hvX hvV
    rcases hvX with rfl | ⟨hvR, _⟩
    · exact hvV.1 rfl
    · exact hvR hvV.2.1
  have hUV : Disjoint U V := by
    rw [Finset.disjoint_left]
    intro v hvU hvV
    simp only [hU, hV, Finset.mem_union, Finset.mem_sdiff, Finset.mem_erase] at hvU hvV
    rcases hvU with h | ⟨_, h⟩
    · exact hvV.2.2 h
    · exact h hvV.2.1
  have hcov : X ∪ U ∪ V = Finset.univ := by
    ext v
    simp only [hX, hU, hV, Finset.mem_union, Finset.mem_insert, Finset.mem_sdiff,
      Finset.mem_univ, true_and, Finset.mem_erase, iff_true]
    by_cases hvR : v ∈ R
    · by_cases hvS : v ∈ S
      · tauto
      · by_cases hvy : v = y
        · tauto
        · tauto
    · by_cases hvA : v ∈ A
      · tauto
      · tauto
  have hnoUV : ∀ u ∈ U, ∀ v ∈ V, ¬ G.Adj u v := by
    intro u hu v hv hadj
    simp only [hU, hV, Finset.mem_union, Finset.mem_sdiff, Finset.mem_erase] at hu hv
    obtain ⟨hvy, hvR, hvS⟩ := hv
    rcases hu with huS | ⟨huA, _⟩
    · have hvx : v ≠ x := fun h => hvS (h ▸ hxS)
      exact hvS (hstep u huS v hvR hadj (fun h => hvy h.2) (fun h => hvx h.2))
    · exact hnoAB u huA v (hWB v hvR hvS hvy) hadj
  have hbound := hsep X U V hUne hVne hXU hXV hUV hcov hnoUV
  -- counting: |X| ≤ 1 + (2k - (|A| - 1)) < 2k
  have hAsub : A ⊆ insert x (A \ R) := by
    intro a ha
    by_cases haR : a ∈ R
    · exact Finset.mem_insert.mpr (Or.inl (hAR a ha haR))
    · exact Finset.mem_insert_of_mem (by simp [ha, haR])
  have c1 := Finset.card_le_card hAsub
  have c2 := Finset.card_insert_le x (A \ R)
  have c3 : X.card ≤ ((Finset.univ \ R) \ A).card + 1 := by
    rw [hX]; exact Finset.card_insert_le _ _
  have hsplit : (Finset.univ \ R) = ((Finset.univ \ R) \ A) ∪ (A \ R) := by
    ext v; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]; tauto
  have hdisj : Disjoint ((Finset.univ \ R) \ A) (A \ R) := by
    rw [Finset.disjoint_left]; intro v h1 h2
    simp only [Finset.mem_sdiff] at h1 h2; exact h1.2 h2.1
  have c4 : (Finset.univ \ R).card = ((Finset.univ \ R) \ A).card + (A \ R).card := by
    rw [← Finset.card_union_of_disjoint hdisj, ← hsplit]
  have c5 : (Finset.univ \ R).card = 2*k := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ R), Finset.card_univ, Fintype.card_fin, hR]
    omega
  clear_value S X U V
  omega
