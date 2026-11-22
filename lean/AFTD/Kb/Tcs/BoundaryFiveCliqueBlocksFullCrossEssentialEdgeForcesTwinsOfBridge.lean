import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.KExtendableEssentialEdgeHasForcedMatchingResidual
import AFTD.Kb.Tcs.PerfectMatchingForcedEdgeInEveryMatching
import AFTD.Kb.Tcs.PerfectMatchingBridgeEvenShoresOnFinset
import AFTD.Kb.Tcs.AnticompleteNeighborDefectBound
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# boundary_five_clique_blocks_full_cross_essential_edge_forces_twins_of_bridge

Topic: graphs   Node: 4ef6d2447f31

Provenance: helper lemma. OP-1957: four-block boundary route, state/campaigns/op1957-in1122-four-block-boundary.md (same-shore count argument); the bridge hypothesis is the stated boundary_five_small_clique_blocks_forced_cross_edge_is_bridge.

Conditional form of boundary_five_clique_blocks_full_cross_essential_edge_forces_twins: in the size-five four-clique boundary partition of a 2k-connected k-extendible graph with degree at least 2k+2, if x in the first five-block is adjacent to all of the second five-block, the edge xy to that block is essential, and every forced xy edge of a matchable 2k-residual is a bridge of it, then two other first-block vertices p,q are true twins missing y and a common vertex z of the opposite large block, which x also misses.
-/

theorem boundary_five_clique_blocks_full_cross_essential_edge_forces_twins_of_bridge
    (k : ℕ) (hk : 5 ≤ k) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hA : A.card=5) (hC : C.card=5)
    (hsizeAB : A.card+B.card=2*k) (hsizeCD : C.card+D.card=2*k)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ c ∈ C, ∀ d ∈ D, ¬ G.Adj c d)
    (hclique : ∀ T ∈ [A,B,C,D], ∀ u ∈ T, ∀ v ∈ T, u ≠ v → G.Adj u v)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (hsep : ∀ X U V : Finset (Fin (4*k)), U.Nonempty → V.Nonempty →
      Disjoint X U → Disjoint X V → Disjoint U V → X ∪ U ∪ V = Finset.univ →
      (∀ u ∈ U, ∀ v ∈ V, ¬ G.Adj u v) → 2*k ≤ X.card)
    (hext : is_k_extendable G k) (x y : Fin (4*k)) (hx : x ∈ A) (hy : y ∈ C)
    (hfull : ∀ w ∈ C, G.Adj x w)
    (hess : ¬ is_k_extendable (G.deleteEdges {s(x,y)}) k)
    (hbr : ∀ R : Finset (Fin (4*k)), R.card = 2*k → ∀ (hxR : x ∈ R) (hyR : y ∈ R),
      (∃ P : (G.induce {v | v ∈ R}).Subgraph, P.IsPerfectMatching) →
      (¬ ∃ P : ((G.induce {v | v ∈ R}).deleteEdges
        {s(⟨x,hxR⟩,⟨y,hyR⟩)}).Subgraph, P.IsPerfectMatching) →
      ¬ ((G.induce {v | v ∈ R}).deleteEdges
        {s(⟨x,hxR⟩,⟨y,hyR⟩)}).Reachable ⟨x,hxR⟩ ⟨y,hyR⟩) :
    ∃ p ∈ A, ∃ q ∈ A, ∃ z ∈ D,
      p ≠ q ∧ p ≠ x ∧ q ≠ x ∧ ¬ G.Adj p y ∧ ¬ G.Adj q y ∧
      ¬ G.Adj x z ∧ ¬ G.Adj p z ∧ ¬ G.Adj q z ∧
      (∀ w, w ≠ p → w ≠ q → (G.Adj p w ↔ G.Adj q w)) := by
  classical
  have hcA : ∀ u ∈ A, ∀ v ∈ A, u ≠ v → G.Adj u v := hclique A (by simp)
  have hcB : ∀ u ∈ B, ∀ v ∈ B, u ≠ v → G.Adj u v := hclique B (by simp)
  have hcC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → G.Adj u v := hclique C (by simp)
  have hcD : ∀ u ∈ D, ∀ v ∈ D, u ≠ v → G.Adj u v := hclique D (by simp)
  have hxy : G.Adj x y := hfull y hy
  obtain ⟨R, hRc, hxR, hyR, ⟨P, hP⟩, hforced⟩ :=
    k_extendable_essential_edge_has_forced_matching_residual (4*k) k G x y hxy hext hess
  have hR : R.card = 2*k := by omega
  have hnr := hbr R hR hxR hyR ⟨P,hP⟩ hforced
  have hPxy : P.Adj ⟨x,hxR⟩ ⟨y,hyR⟩ :=
    perfect_matching_forced_edge_in_every_matching _ _ _ hforced P hP
  obtain ⟨Q, W, hQW, hcov, hxQ, hyQ, hxW, hyW, -, -, hyQadj, hxWadj, hQWadj⟩ :=
    perfect_matching_bridge_even_shores_on_finset G R x y hxR hyR P hP hPxy hnr
  have hxy' : x ≠ y := hxy.ne
  -- block membership
  have hmem : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ C ∨ v ∈ D := by
    intro v
    have : v ∈ A ∪ B ∪ C ∪ D := by rw [hcover]; exact Finset.mem_univ v
    simp only [Finset.mem_union] at this
    rcases this with ((h | h) | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have nAB : ∀ v, v ∈ A → v ∉ B := fun v h => Finset.disjoint_left.mp hAB h
  have nAC : ∀ v, v ∈ A → v ∉ C := fun v h => Finset.disjoint_left.mp hAC h
  have nAD : ∀ v, v ∈ A → v ∉ D := fun v h => Finset.disjoint_left.mp hAD h
  have nBC : ∀ v, v ∈ B → v ∉ C := fun v h => Finset.disjoint_left.mp hBC h
  have nBD : ∀ v, v ∈ B → v ∉ D := fun v h => Finset.disjoint_left.mp hBD h
  have nCD : ∀ v, v ∈ C → v ∉ D := fun v h => Finset.disjoint_left.mp hCD h
  have nQW : ∀ v, v ∈ Q → v ∉ W := fun v h => Finset.disjoint_left.mp hQW h
  have hQR : ∀ v, v ∈ Q → v ∈ R := fun v h => by rw [← hcov]; simp [h]
  have hWR : ∀ v, v ∈ W → v ∈ R := fun v h => by rw [← hcov]; simp [h]
  have hRmem : ∀ v, v ∈ R → v ∈ Q ∨ v ∈ W ∨ v = x ∨ v = y := by
    intro v hv
    rw [← hcov] at hv
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with (h | h) | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hCQ : ∀ c ∈ C, c ∉ Q := by
    intro c hc hcQ
    have hcy : c ≠ y := fun h => hyQ (h ▸ hcQ)
    exact hyQadj c hcQ (hcC y hy c hc hcy.symm)
  have hCW : ∀ c ∈ C, c ∉ W := fun c hc hcW => hxWadj c hcW (hfull c hc)
  have hAW : ∀ a ∈ A, a ∉ W := by
    intro a ha haW
    have hax : a ≠ x := fun h => hxW (h ▸ haW)
    exact hxWadj a haW (hcA x hx a ha hax.symm)
  have hBsplit : ∀ b ∈ B, ∀ b' ∈ B, b ∈ Q → b' ∈ W → False := by
    intro b hb b' hb' hbQ hb'W
    have hne : b ≠ b' := fun h => nQW b hbQ (h ▸ hb'W)
    exact hQWadj b hbQ b' hb'W (hcB b hb b' hb' hne)
  have hDsplit : ∀ d ∈ D, ∀ d' ∈ D, d ∈ Q → d' ∈ W → False := by
    intro d hd d' hd' hdQ hd'W
    have hne : d ≠ d' := fun h => nQW d hdQ (h ▸ hd'W)
    exact hQWadj d hdQ d' hd'W (hcD d hd d' hd' hne)
  -- cardinalities
  have hQeq : Q = (A ∩ Q) ∪ (B ∩ Q) ∪ (D ∩ Q) := by
    ext v
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro hv
      rcases hmem v with h | h | h | h
      · exact Or.inl (Or.inl ⟨h, hv⟩)
      · exact Or.inl (Or.inr ⟨h, hv⟩)
      · exact absurd hv (hCQ v h)
      · exact Or.inr ⟨h, hv⟩
    · rintro ((⟨-, h⟩ | ⟨-, h⟩) | ⟨-, h⟩) <;> exact h
  have hWeq : W = (B ∩ W) ∪ (D ∩ W) := by
    ext v
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro hv
      rcases hmem v with h | h | h | h
      · exact absurd hv (hAW v h)
      · exact Or.inl ⟨h, hv⟩
      · exact absurd hv (hCW v h)
      · exact Or.inr ⟨h, hv⟩
    · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact h
  have hQc : Q.card = (A ∩ Q).card + (B ∩ Q).card + (D ∩ Q).card := by
    conv_lhs => rw [hQeq]
    rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
    · exact Finset.disjoint_left.mpr fun v h1 h2 =>
        nAB v (Finset.mem_inter.mp h1).1 (Finset.mem_inter.mp h2).1
    · refine Finset.disjoint_left.mpr fun v h1 h2 => ?_
      rcases Finset.mem_union.mp h1 with h1 | h1
      · exact nAD v (Finset.mem_inter.mp h1).1 (Finset.mem_inter.mp h2).1
      · exact nBD v (Finset.mem_inter.mp h1).1 (Finset.mem_inter.mp h2).1
  have hWc : W.card = (B ∩ W).card + (D ∩ W).card := by
    conv_lhs => rw [hWeq]
    rw [Finset.card_union_of_disjoint]
    exact Finset.disjoint_left.mpr fun v h1 h2 =>
      nBD v (Finset.mem_inter.mp h1).1 (Finset.mem_inter.mp h2).1
  have hRc2 : R.card = Q.card + W.card + 2 := by
    rw [← hcov, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint hQW,
      Finset.card_pair hxy']
    refine Finset.disjoint_left.mpr fun v h1 h2 => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at h2
    rcases h2 with rfl | rfl <;> rcases Finset.mem_union.mp h1 with h1 | h1
    exacts [hxQ h1, hxW h1, hyQ h1, hyW h1]
  -- defect budgets
  have hBcard : B.card = 2*k-5 := by omega
  have hDcard : D.card = 2*k-5 := by omega
  have hbudA : ∀ a ∈ A, (((Finset.univ \ B).erase a) \ G.neighborFinset a).card ≤ 2 := by
    intro a ha
    refine anticomplete_neighbor_defect_bound G B a (nAB a ha) (hnoAB a ha) (2*k+4) 2 ?_ ?_
    · simp only [Fintype.card_fin]; omega
    · have := hdegree a; omega
  have hbudC : ∀ c ∈ C, (((Finset.univ \ D).erase c) \ G.neighborFinset c).card ≤ 2 := by
    intro c hc
    refine anticomplete_neighbor_defect_bound G D c (nCD c hc) (hnoCD c hc) (2*k+4) 2 ?_ ?_
    · simp only [Fintype.card_fin]; omega
    · have := hdegree c; omega
  have hy2 : (A ∩ Q).card + (B ∩ Q).card ≤ 2 := by
    have hsub : (A ∩ Q) ∪ (B ∩ Q) ⊆ ((Finset.univ \ D).erase y) \ G.neighborFinset y := by
      intro v hv
      have hvQ : v ∈ Q := by
        rcases Finset.mem_union.mp hv with h | h <;> exact (Finset.mem_inter.mp h).2
      have hvD : v ∉ D := by
        rcases Finset.mem_union.mp hv with h | h
        · exact nAD v (Finset.mem_inter.mp h).1
        · exact nBD v (Finset.mem_inter.mp h).1
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, true_and,
        SimpleGraph.mem_neighborFinset]
      exact ⟨⟨fun h => hyQ (h ▸ hvQ), hvD⟩, hyQadj v hvQ⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint] at h1
    · exact h1.trans (hbudC y hy)
    · exact Finset.disjoint_left.mpr fun v h1 h2 =>
        nAB v (Finset.mem_inter.mp h1).1 (Finset.mem_inter.mp h2).1
  have hpbud : ∀ p ∈ A ∩ Q, insert y (D ∩ W) ⊆ ((Finset.univ \ B).erase p) \ G.neighborFinset p := by
    intro p hp
    obtain ⟨hpA, hpQ⟩ := Finset.mem_inter.mp hp
    intro v hv
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, true_and,
      SimpleGraph.mem_neighborFinset]
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact ⟨⟨fun h => hyQ (h ▸ hpQ), fun h => nBC v h hy⟩, fun h => hyQadj p hpQ h.symm⟩
    · obtain ⟨hvD, hvW⟩ := Finset.mem_inter.mp hv
      exact ⟨⟨fun h => nQW p hpQ (h ▸ hvW), fun h => nBD v h hvD⟩, hQWadj p hpQ v hvW⟩
  have hyDW : y ∉ D ∩ W := fun h => nCD y hy (Finset.mem_inter.mp h).1
  have hp2 : (A ∩ Q).Nonempty → (D ∩ W).card ≤ 1 := by
    rintro ⟨p, hp⟩
    have h1 := Finset.card_le_card (hpbud p hp)
    rw [Finset.card_insert_of_notMem hyDW] at h1
    have := hbudA p (Finset.mem_inter.mp hp).1
    omega
  have hx2 : (D ∩ W).card ≤ 2 := by
    have hsub : D ∩ W ⊆ ((Finset.univ \ B).erase x) \ G.neighborFinset x := by
      intro v hv
      obtain ⟨hvD, hvW⟩ := Finset.mem_inter.mp hv
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, true_and,
        SimpleGraph.mem_neighborFinset]
      exact ⟨⟨fun h => hxW (h ▸ hvW), fun h => nBD v h hvD⟩, hxWadj v hvW⟩
    exact (Finset.card_le_card hsub).trans (hbudA x hx)
  have hBQW : (B ∩ Q).card = 0 ∨ (B ∩ W).card = 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc.1)
    obtain ⟨b', hb'⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc.2)
    exact hBsplit b (Finset.mem_inter.mp hb).1 b' (Finset.mem_inter.mp hb').1
      (Finset.mem_inter.mp hb).2 (Finset.mem_inter.mp hb').2
  have hDQW : (D ∩ Q).card = 0 ∨ (D ∩ W).card = 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc.1)
    obtain ⟨b', hb'⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc.2)
    exact hDsplit b (Finset.mem_inter.mp hb).1 b' (Finset.mem_inter.mp hb').1
      (Finset.mem_inter.mp hb).2 (Finset.mem_inter.mp hb').2
  have hBle : (B ∩ Q).card + (B ∩ W).card ≤ 2*k-5 := by
    rw [← hBcard, ← Finset.card_union_of_disjoint]
    · exact Finset.card_le_card (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
    · exact Finset.disjoint_left.mpr fun v h1 h2 => nQW v (Finset.mem_inter.mp h1).2 (Finset.mem_inter.mp h2).2
  have hDle : (D ∩ Q).card + (D ∩ W).card ≤ 2*k-5 := by
    rw [← hDcard, ← Finset.card_union_of_disjoint]
    · exact Finset.card_le_card (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
    · exact Finset.disjoint_left.mpr fun v h1 h2 => nQW v (Finset.mem_inter.mp h1).2 (Finset.mem_inter.mp h2).2
  -- separator case
  have hsepc : ¬ (0 < (D ∩ Q).card ∧ 0 < (B ∩ W).card) := by
    rintro ⟨hdq, hbw⟩
    have hbq : (B ∩ Q).card = 0 := by omega
    have hdw : (D ∩ W).card = 0 := by omega
    have hbq' : ∀ v ∈ B, v ∉ Q := fun v hv hvQ => by
      rw [Finset.card_eq_zero] at hbq
      exact (Finset.eq_empty_iff_forall_notMem.mp hbq) v (Finset.mem_inter.mpr ⟨hv, hvQ⟩)
    have hdw' : ∀ v ∈ D, v ∉ W := fun v hv hvW => by
      rw [Finset.card_eq_zero] at hdw
      exact (Finset.eq_empty_iff_forall_notMem.mp hdw) v (Finset.mem_inter.mpr ⟨hv, hvW⟩)
    let X := A ∪ (B \ R) ∪ (D \ R)
    let U := (B ∩ R) ∪ C
    let V' := D ∩ R
    have hBR : ∀ v ∈ B, v ∈ R → v ∈ W := by
      intro v hv hvR
      rcases hRmem v hvR with h | h | h | h
      · exact absurd h (hbq' v hv)
      · exact h
      · exact absurd (h ▸ hx) (fun h' => nAB v h' hv)
      · exact absurd (h ▸ hy) (nBC v hv)
    have hDR : ∀ v ∈ D, v ∈ R → v ∈ Q := by
      intro v hv hvR
      rcases hRmem v hvR with h | h | h | h
      · exact h
      · exact absurd h (hdw' v hv)
      · exact absurd (h ▸ hx) (fun h' => nAD v h' hv)
      · exact absurd (h ▸ hy) (fun h' => nCD v h' hv)
    have hUne : U.Nonempty := ⟨y, Finset.mem_union.mpr (Or.inr hy)⟩
    have hVne : V'.Nonempty := by
      obtain ⟨d, hd⟩ := Finset.card_pos.mp hdq
      exact ⟨d, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hd).1, hQR d (Finset.mem_inter.mp hd).2⟩⟩
    have hXU : Disjoint X U := by
      refine Finset.disjoint_left.mpr fun v h1 h2 => ?_
      simp only [X, U, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter] at h1 h2
      rcases h1 with (h1 | h1) | h1 <;> rcases h2 with h2 | h2
      · exact nAB v h1 h2.1
      · exact nAC v h1 h2
      · exact h1.2 h2.2
      · exact nBC v h1.1 h2
      · exact nBD v h2.1 h1.1
      · exact nCD v h2 h1.1
    have hXV : Disjoint X V' := by
      refine Finset.disjoint_left.mpr fun v h1 h2 => ?_
      simp only [X, V', Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter] at h1 h2
      rcases h1 with (h1 | h1) | h1
      · exact nAD v h1 h2.1
      · exact nBD v h1.1 h2.1
      · exact h1.2 h2.2
    have hUV : Disjoint U V' := by
      refine Finset.disjoint_left.mpr fun v h1 h2 => ?_
      simp only [U, V', Finset.mem_union, Finset.mem_inter] at h1 h2
      rcases h1 with h1 | h1
      · exact nBD v h1.1 h2.1
      · exact nCD v h1 h2.1
    have hXUV : X ∪ U ∪ V' = Finset.univ := by
      rw [Finset.eq_univ_iff_forall]
      intro v
      rcases hmem v with h | h | h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
      · by_cases hv : v ∈ R
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨h, hv⟩)))
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h, hv⟩))))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_right _ h))
      · by_cases hv : v ∈ R
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨h, hv⟩)
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h, hv⟩)))
    have hanti : ∀ u ∈ U, ∀ v ∈ V', ¬ G.Adj u v := by
      intro u hu v hv
      simp only [U, V', Finset.mem_union, Finset.mem_inter] at hu hv
      rcases hu with hu | hu
      · intro h
        exact hQWadj v (hDR v hv.1 hv.2) u (hBR u hu.1 hu.2) h.symm
      · exact hnoCD u hu v hv.1
    have hXc := hsep X U V' hUne hVne hXU hXV hUV hXUV hanti
    have hX1 : X.card ≤ A.card + (B \ R).card + (D \ R).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    have hB1 := Finset.card_sdiff_add_card_inter B R
    have hD1 := Finset.card_sdiff_add_card_inter D R
    have hB2 : (B ∩ W).card ≤ (B ∩ R).card :=
      Finset.card_le_card fun v hv => Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hv).1, hWR v (Finset.mem_inter.mp hv).2⟩
    have hD2 : (D ∩ Q).card ≤ (D ∩ R).card :=
      Finset.card_le_card fun v hv => Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hv).1, hQR v (Finset.mem_inter.mp hv).2⟩
    omega
  -- the arithmetic
  have hAQne : (A ∩ Q).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have h0 : (A ∩ Q).card = 0 := by rw [hne]; rfl
    omega
  have hdw1 := hp2 hAQne
  have hAQ2 : (A ∩ Q).card = 2 := by omega
  have hDW1 : (D ∩ W).card = 1 := by omega
  obtain ⟨p, q, hpq, hpqeq⟩ := Finset.card_eq_two.mp hAQ2
  obtain ⟨z, hzeq⟩ := Finset.card_eq_one.mp hDW1
  have hpAQ : p ∈ A ∩ Q := by rw [hpqeq]; simp
  have hqAQ : q ∈ A ∩ Q := by rw [hpqeq]; simp
  have hzDW : z ∈ D ∩ W := by rw [hzeq]; simp
  obtain ⟨hpA, hpQ⟩ := Finset.mem_inter.mp hpAQ
  obtain ⟨hqA, hqQ⟩ := Finset.mem_inter.mp hqAQ
  obtain ⟨hzD, hzW⟩ := Finset.mem_inter.mp hzDW
  -- exact defect sets
  have hexact : ∀ t ∈ A ∩ Q,
      ((Finset.univ \ B).erase t) \ G.neighborFinset t = insert y (D ∩ W) := by
    intro t ht
    symm
    apply Finset.eq_of_subset_of_card_le (hpbud t ht)
    rw [Finset.card_insert_of_notMem hyDW, hDW1]
    exact hbudA t (Finset.mem_inter.mp ht).1
  have hchar : ∀ t ∈ A ∩ Q, ∀ w, w ∉ B → w ≠ t → (¬ G.Adj t w ↔ (w = y ∨ w = z)) := by
    intro t ht w hwB hwt
    have h := congrArg (fun S => w ∈ S) (hexact t ht)
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, true_and,
      SimpleGraph.mem_neighborFinset, Finset.mem_insert, hzeq, Finset.mem_singleton] at h
    rw [← h]
    simp [hwt, hwB]
  refine ⟨p, hpA, q, hqA, z, hzD, hpq, fun h => hxQ (h ▸ hpQ), fun h => hxQ (h ▸ hqQ),
    fun h => hyQadj p hpQ h.symm, fun h => hyQadj q hqQ h.symm, hxWadj z hzW,
    hQWadj p hpQ z hzW, hQWadj q hqQ z hzW, ?_⟩
  intro w hwp hwq
  by_cases hwB : w ∈ B
  · exact ⟨fun h => absurd h (hnoAB p hpA w hwB), fun h => absurd h (hnoAB q hqA w hwB)⟩
  · have h1 := hchar p hpAQ w hwB hwp
    have h2 := hchar q hqAQ w hwB hwq
    constructor
    · intro h
      by_contra h'
      exact (h1.mpr (h2.mp h')) h
    · intro h
      by_contra h'
      exact (h2.mpr (h1.mp h')) h
