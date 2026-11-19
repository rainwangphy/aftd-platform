import AFTD.Prelude
import AFTD.Kb.Tcs.IsMinimallyKExtendable
import AFTD.Kb.Tcs.IsKExtendable

/-!
# minimally_k_extendable_order_two_mul_add_six_min_degree_le

Topic: graphs   Node: 9760c4892e19

Provenance: original. Related work: OP-1957 (arXiv:2611.22690, Conjecture 1.1) at order nu = 2k+6, every k >= 3; the paper proves the case k = 3 (order 12, Lemmas 5.7-5.11) by a longer case analysis. No connectedness hypothesis is needed: minimum degree >= 2k+2 on 2k+6 vertices forces it.

For every k ≥ 3 and every simple graph G on Fin (2k+6) (with decidable adjacency) that is minimally k-extendable (is_minimally_k_extendable G k), the minimum degree G.minDegree is at most 2k + 1.
-/

theorem minimally_k_extendable_order_two_mul_add_six_min_degree_le : ∀ k : ℕ, 3 ≤ k → ∀ G : SimpleGraph (Fin (2 * k + 6)), ∀ [DecidableRel G.Adj],
    is_minimally_k_extendable G k → G.minDegree ≤ 2 * k + 1 := by
  have key : ∀ x02 x03 x04 x05 x12 x13 x14 x15 x24 x25 x34 x35 : Bool,
      (x02 = true → x12 = true → False) →
      (x03 = true → x13 = true → False) →
      (x04 = true → x14 = true → False) →
      (x05 = true → x15 = true → False) →
      (x02 = true → x03 = true → x14 = true → x15 = true → x24 = true → x25 = true → x34 = true → x35 = true → False) →
      (x04 = true → x05 = true → x12 = true → x13 = true → x24 = true → x25 = true → x34 = true → x35 = true → False) →
      (x02 = true → x03 = true → x04 = true → x05 = true → False) →
      (x12 = true → x13 = true → x14 = true → x15 = true → False) →
      (x02 = true → x12 = true → x24 = true → x25 = true → False) →
      (x03 = true → x13 = true → x34 = true → x35 = true → False) →
      (x04 = true → x14 = true → x24 = true → x34 = true → False) →
      (x05 = true → x15 = true → x25 = true → x35 = true → False) →
      (x02 = false ∧ x13 = false) ∨
      (x02 = false ∧ x14 = false ∧ x35 = false) ∨
      (x02 = false ∧ x15 = false ∧ x34 = false) ∨
      (x03 = false ∧ x12 = false) ∨
      (x03 = false ∧ x14 = false ∧ x25 = false) ∨
      (x03 = false ∧ x15 = false ∧ x24 = false) ∨
      (x04 = false ∧ x12 = false ∧ x35 = false) ∨
      (x04 = false ∧ x13 = false ∧ x25 = false) ∨
      (x04 = false ∧ x15 = false) ∨
      (x05 = false ∧ x12 = false ∧ x34 = false) ∨
      (x05 = false ∧ x13 = false ∧ x24 = false) ∨
      (x05 = false ∧ x14 = false) := by
    set_option synthInstance.maxSize 100000 in
    set_option synthInstance.maxHeartbeats 2000000 in
    decide

  classical
  intro k hk G _ hmin
  by_contra hcon
  have hδ : 2 * k + 2 ≤ G.minDegree := by omega
  obtain ⟨⟨hcard, ⟨M0, hM0, hM0k⟩, hext⟩, hminimal⟩ := hmin
  have Hsymm : ∀ x y : Fin (2 * k + 6), (x ≠ y ∧ ¬ G.Adj x y) → (y ≠ x ∧ ¬ G.Adj y x) :=
    fun x y h => ⟨h.1.symm, fun h' => h.2 h'.symm⟩
  have hadj : ∀ x y : Fin (2 * k + 6), x ≠ y → decide (x ≠ y ∧ ¬ G.Adj x y) = false → G.Adj x y := by
    intro x y hxy h
    have h' := of_decide_eq_false h
    by_contra hG
    exact h' ⟨hxy, hG⟩
  have hNex : ∀ x : Fin (2 * k + 6), ∃ N : Finset (Fin (2 * k + 6)), (∀ y, y ∈ N ↔ (x ≠ y ∧ ¬ G.Adj x y)) ∧ N.card ≤ 3 := by
    intro x
    refine ⟨Finset.univ \ insert x (G.neighborFinset x), ?_, ?_⟩
    · intro y
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨fun h => h1 h.symm, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨fun h => h1 h.symm, h2⟩
    · have h1 : 2 * k + 2 ≤ G.degree x := le_trans hδ (G.minDegree_le_degree x)
      rw [Finset.card_univ_sdiff, Fintype.card_fin, Finset.card_insert_of_notMem (by simp),
        SimpleGraph.card_neighborFinset_eq_degree]
      omega
  choose N hNmem hNcard using hNex
  have L3 : ∀ (s : Finset (Fin (2 * k + 6))) (x y z w : Fin (2 * k + 6)), s.card ≤ 3 → x ∈ s → y ∈ s → z ∈ s →
      x ≠ y → x ≠ z → y ≠ z → w ∈ s → w = x ∨ w = y ∨ w = z := by
    intro s x y z w hs hx hy hz hxy hxz hyz hw
    have hc : ({x, y, z} : Finset (Fin (2 * k + 6))).card = 3 := Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩
    have hsub : ({x, y, z} : Finset (Fin (2 * k + 6))) ⊆ s := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl <;> assumption
    have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
    rw [← heq] at hw
    simpa using hw
  have hdeg : ∀ x y1 y2 y3 y4 : Fin (2 * k + 6), y1 ≠ y2 → y1 ≠ y3 → y1 ≠ y4 → y2 ≠ y3 → y2 ≠ y4 → y3 ≠ y4 →
      (x ≠ y1 ∧ ¬ G.Adj x y1) → (x ≠ y2 ∧ ¬ G.Adj x y2) → (x ≠ y3 ∧ ¬ G.Adj x y3) → (x ≠ y4 ∧ ¬ G.Adj x y4) → False := by
    intro x y1 y2 y3 y4 h12 h13 h14 h23 h24 h34 h1 h2 h3 h4
    rcases L3 (N x) y1 y2 y3 y4 (hNcard x) ((hNmem x y1).mpr h1) ((hNmem x y2).mpr h2)
      ((hNmem x y3).mpr h3) h12 h13 h23 ((hNmem x y4).mpr h4) with h | h | h
    · exact h14 h.symm
    · exact h24 h.symm
    · exact h34 h.symm
  have hVB : ∀ M : G.Subgraph, M.IsMatching → M.edgeSet.ncard = k →
      ∃ S : Finset (Fin (2 * k + 6)), (∀ x, x ∈ M.verts → x ∈ S) ∧ S.card ≤ 2 * k := by
    intro M hM hMk
    refine ⟨(M.edgeSet.toFinite.toFinset).biUnion (fun e => e.toFinset), ?_, ?_⟩
    · intro x hx
      obtain ⟨w, hw, -⟩ := hM hx
      rw [Finset.mem_biUnion]
      exact ⟨s(x, w), by simpa using hw, by simp⟩
    · have h1 : ((M.edgeSet.toFinite.toFinset).biUnion (fun e => e.toFinset)).card ≤
          (M.edgeSet.toFinite.toFinset).card * 2 := by
        apply Finset.card_biUnion_le_card_mul
        intro e _
        rw [Sym2.card_toFinset]
        split_ifs <;> omega
      have h2 : (M.edgeSet.toFinite.toFinset).card = k := by
        rw [← Set.ncard_eq_toFinset_card M.edgeSet M.edgeSet.toFinite, hMk]
      omega
  obtain ⟨S0, hS0, hS0c⟩ := hVB M0 hM0 hM0k
  obtain ⟨u, hu⟩ : ∃ u : Fin (2 * k + 6), u ∉ S0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have h1 : S0 = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    rw [h1, Finset.card_univ, Fintype.card_fin] at hS0c
    omega
  have huM0 : u ∉ M0.verts := fun h => hu (hS0 u h)
  have hBad : (insert u (N u ∪ (N u).biUnion (fun x => (N x).erase u))).card ≤ 10 := by
    have h1 : ((N u).biUnion (fun x => (N x).erase u)).card ≤ (N u).card * 2 := by
      apply Finset.card_biUnion_le_card_mul
      intro x hx
      have hux : u ∈ N x := (hNmem x u).mpr (Hsymm _ _ ((hNmem u x).mp hx))
      rw [Finset.card_erase_of_mem hux]
      have := hNcard x
      omega
    have h2 := Finset.card_union_le (N u) ((N u).biUnion (fun x => (N x).erase u))
    have h3 := Finset.card_insert_le u (N u ∪ (N u).biUnion (fun x => (N x).erase u))
    have h4 := hNcard u
    omega
  have hgood : 1 < (Finset.univ \ (insert u (N u ∪ (N u).biUnion (fun x => (N x).erase u)))).card := by
    rw [Finset.card_univ_sdiff, Fintype.card_fin]
    omega
  obtain ⟨v1, hv1, v2, hv2, hv12⟩ := Finset.one_lt_card.mp hgood
  have hprop : ∀ v, v ∈ Finset.univ \ (insert u (N u ∪ (N u).biUnion (fun x => (N x).erase u))) →
      G.Adj u v ∧ ∀ w, (u ≠ w ∧ ¬ G.Adj u w) → ¬ (v ≠ w ∧ ¬ G.Adj v w) := by
    intro v hv
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_union,
      Finset.mem_biUnion, Finset.mem_erase, not_or] at hv
    obtain ⟨hvu, hvN, hvB⟩ := hv
    have hG : G.Adj u v := by
      by_contra hG
      exact hvN ((hNmem u v).mpr ⟨fun h => hvu h.symm, hG⟩)
    exact ⟨hG, fun w hw hvw => hvB ⟨w, (hNmem u w).mpr hw, hvu, (hNmem w v).mpr (Hsymm _ _ hvw)⟩⟩
  have hBex : ∀ v1 v2 : Fin (2 * k + 6), v1 ≠ v2 → G.Adj u v1 → G.Adj u v2 → (∃ b1 b2 a1 a2 : Fin (2 * k + 6), b1 ≠ b2 ∧ a1 ≠ a2 ∧ (u ≠ b1 ∧ ¬ G.Adj u b1) ∧ (u ≠ b2 ∧ ¬ G.Adj u b2) ∧ (v1 ≠ a1 ∧ ¬ G.Adj v1 a1) ∧ (v1 ≠ a2 ∧ ¬ G.Adj v1 a2) ∧ (a1 ≠ b1 ∧ ¬ G.Adj a1 b1) ∧ (a1 ≠ b2 ∧ ¬ G.Adj a1 b2) ∧ (a2 ≠ b1 ∧ ¬ G.Adj a2 b1) ∧ (a2 ≠ b2 ∧ ¬ G.Adj a2 b2)) → (∃ b1 b2 a1 a2 : Fin (2 * k + 6), b1 ≠ b2 ∧ a1 ≠ a2 ∧ (u ≠ b1 ∧ ¬ G.Adj u b1) ∧ (u ≠ b2 ∧ ¬ G.Adj u b2) ∧ (v2 ≠ a1 ∧ ¬ G.Adj v2 a1) ∧ (v2 ≠ a2 ∧ ¬ G.Adj v2 a2) ∧ (a1 ≠ b1 ∧ ¬ G.Adj a1 b1) ∧ (a1 ≠ b2 ∧ ¬ G.Adj a1 b2) ∧ (a2 ≠ b1 ∧ ¬ G.Adj a2 b1) ∧ (a2 ≠ b2 ∧ ¬ G.Adj a2 b2)) → False := by
    rintro v1 v2 hv12 hG1 hG2 ⟨b1, b2, a1, a2, hb, ha, hub1, hub2, hva1, hva2, h11, h12, h21, h22⟩
      ⟨c1, c2, d1, d2, hc, hd, huc1, huc2, hvd1, hvd2, k11, k12, k21, k22⟩
    have s1 : ∃ b : Fin (2 * k + 6), (u ≠ b ∧ ¬ G.Adj u b) ∧ (a1 ≠ b ∧ ¬ G.Adj a1 b) ∧ (a2 ≠ b ∧ ¬ G.Adj a2 b) ∧ (d1 ≠ b ∧ ¬ G.Adj d1 b) ∧ (d2 ≠ b ∧ ¬ G.Adj d2 b) := by
      by_cases e1 : c1 = b1
      · subst e1; exact ⟨_, hub1, h11, h21, k11, k21⟩
      by_cases e2 : c1 = b2
      · subst e2; exact ⟨_, hub2, h12, h22, k11, k21⟩
      rcases L3 (N u) b1 b2 c1 c2 (hNcard u) ((hNmem u b1).mpr hub1) ((hNmem u b2).mpr hub2)
        ((hNmem u c1).mpr huc1) hb (Ne.symm e1) (Ne.symm e2) ((hNmem u c2).mpr huc2) with e | e | e
      · subst e; exact ⟨_, hub1, h11, h21, k12, k22⟩
      · subst e; exact ⟨_, hub2, h12, h22, k12, k22⟩
      · exact absurd e.symm hc
    obtain ⟨b, hub, ha1b, ha2b, hd1b, hd2b⟩ := s1
    have hua1 : u ≠ a1 := fun h => hva1.2 (h ▸ hG1.symm)
    have hua2 : u ≠ a2 := fun h => hva2.2 (h ▸ hG1.symm)
    have hud1 : u ≠ d1 := fun h => hvd1.2 (h ▸ hG2.symm)
    have s2 : ∃ a : Fin (2 * k + 6), (v1 ≠ a ∧ ¬ G.Adj v1 a) ∧ (a ≠ b1 ∧ ¬ G.Adj a b1) ∧ (a ≠ b2 ∧ ¬ G.Adj a b2) ∧ (v2 ≠ a ∧ ¬ G.Adj v2 a) := by
      rcases L3 (N b) u a1 a2 d1 (hNcard b) ((hNmem b u).mpr (Hsymm _ _ hub)) ((hNmem b a1).mpr (Hsymm _ _ ha1b))
        ((hNmem b a2).mpr (Hsymm _ _ ha2b)) hua1 hua2 ha ((hNmem b d1).mpr (Hsymm _ _ hd1b)) with e | e | e
      · exact absurd e.symm hud1
      · subst e; exact ⟨_, hva1, h11, h12, hvd1⟩
      · subst e; exact ⟨_, hva2, h21, h22, hvd1⟩
    obtain ⟨a, hv1a, hab1, hab2, hv2a⟩ := s2
    have hb1v1 : b1 ≠ v1 := fun h => hub1.2 (h ▸ hG1)
    have hb2v1 : b2 ≠ v1 := fun h => hub2.2 (h ▸ hG1)
    rcases L3 (N a) b1 b2 v1 v2 (hNcard a) ((hNmem a b1).mpr hab1) ((hNmem a b2).mpr hab2)
      ((hNmem a v1).mpr (Hsymm _ _ hv1a)) hb hb1v1 hb2v1 ((hNmem a v2).mpr (Hsymm _ _ hv2a)) with e | e | e
    · exact hub1.2 (e ▸ hG2)
    · exact hub2.2 (e ▸ hG2)
    · exact hv12 e.symm
  obtain ⟨v, hGuv, hnc, hnB⟩ : ∃ v : Fin (2 * k + 6), G.Adj u v ∧ (∀ w, (u ≠ w ∧ ¬ G.Adj u w) → ¬ (v ≠ w ∧ ¬ G.Adj v w)) ∧ ¬ (∃ b1 b2 a1 a2 : Fin (2 * k + 6), b1 ≠ b2 ∧ a1 ≠ a2 ∧ (u ≠ b1 ∧ ¬ G.Adj u b1) ∧ (u ≠ b2 ∧ ¬ G.Adj u b2) ∧ (v ≠ a1 ∧ ¬ G.Adj v a1) ∧ (v ≠ a2 ∧ ¬ G.Adj v a2) ∧ (a1 ≠ b1 ∧ ¬ G.Adj a1 b1) ∧ (a1 ≠ b2 ∧ ¬ G.Adj a1 b2) ∧ (a2 ≠ b1 ∧ ¬ G.Adj a2 b1) ∧ (a2 ≠ b2 ∧ ¬ G.Adj a2 b2)) := by
    by_cases hB1 : (∃ b1 b2 a1 a2 : Fin (2 * k + 6), b1 ≠ b2 ∧ a1 ≠ a2 ∧ (u ≠ b1 ∧ ¬ G.Adj u b1) ∧ (u ≠ b2 ∧ ¬ G.Adj u b2) ∧ (v1 ≠ a1 ∧ ¬ G.Adj v1 a1) ∧ (v1 ≠ a2 ∧ ¬ G.Adj v1 a2) ∧ (a1 ≠ b1 ∧ ¬ G.Adj a1 b1) ∧ (a1 ≠ b2 ∧ ¬ G.Adj a1 b2) ∧ (a2 ≠ b1 ∧ ¬ G.Adj a2 b1) ∧ (a2 ≠ b2 ∧ ¬ G.Adj a2 b2))
    · by_cases hB2 : (∃ b1 b2 a1 a2 : Fin (2 * k + 6), b1 ≠ b2 ∧ a1 ≠ a2 ∧ (u ≠ b1 ∧ ¬ G.Adj u b1) ∧ (u ≠ b2 ∧ ¬ G.Adj u b2) ∧ (v2 ≠ a1 ∧ ¬ G.Adj v2 a1) ∧ (v2 ≠ a2 ∧ ¬ G.Adj v2 a2) ∧ (a1 ≠ b1 ∧ ¬ G.Adj a1 b1) ∧ (a1 ≠ b2 ∧ ¬ G.Adj a1 b2) ∧ (a2 ≠ b1 ∧ ¬ G.Adj a2 b1) ∧ (a2 ≠ b2 ∧ ¬ G.Adj a2 b2))
      · exact (hBex v1 v2 hv12 (hprop v1 hv1).1 (hprop v2 hv2).1 hB1 hB2).elim
      · exact ⟨v2, (hprop v2 hv2).1, (hprop v2 hv2).2, hB2⟩
    · exact ⟨v1, (hprop v1 hv1).1, (hprop v1 hv1).2, hB1⟩
  apply hminimal s(u, v) (by simpa using hGuv)
  have hG' : ∀ x y : Fin (2 * k + 6), (G.deleteEdges {s(u, v)}).Adj x y ↔ G.Adj x y ∧ s(x, y) ≠ s(u, v) := by
    intro x y
    simp [SimpleGraph.deleteEdges_adj]
  have hsym : ∀ x y : Fin (2 * k + 6), s(x, y) = s(u, v) → (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
    intro x y h
    simpa [Sym2.eq_iff] using h
  have hlift0 : ∀ {x y : Fin (2 * k + 6)}, M0.Adj x y → (G.deleteEdges {s(u, v)}).Adj x y := by
    intro x y h
    rw [hG']
    refine ⟨M0.adj_sub h, fun he => ?_⟩
    rcases hsym _ _ he with ⟨hx, -⟩ | ⟨-, hy⟩
    · exact huM0 (hx ▸ M0.edge_vert h)
    · exact huM0 (hy ▸ M0.edge_vert h.symm)
  refine ⟨hcard, ⟨⟨M0.verts, M0.Adj, hlift0, M0.edge_vert, M0.symm⟩, fun x hx => hM0 hx, ?_⟩, ?_⟩
  · refine Eq.trans (congrArg Set.ncard ?_) hM0k
    ext e; induction e using Sym2.ind; exact Iff.rfl
  intro M' hM' hM'k
  have hup : ∀ {x y : Fin (2 * k + 6)}, M'.Adj x y → G.Adj x y := fun h => ((hG' _ _).mp (M'.adj_sub h)).1
  obtain ⟨P, hP, hMP⟩ := hext ⟨M'.verts, M'.Adj, hup, M'.edge_vert, M'.symm⟩ (fun x hx => hM' hx) (Eq.trans (congrArg Set.ncard (by ext e; induction e using Sym2.ind; exact Iff.rfl)) hM'k)
  have hP' := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP
  have hMPadj : ∀ {x y : Fin (2 * k + 6)}, M'.Adj x y → P.Adj x y := fun h => hMP.2 h
  obtain ⟨SM, hSM, hSMc⟩ := hVB ⟨M'.verts, M'.Adj, hup, M'.edge_vert, M'.symm⟩ (fun x hx => hM' hx) (Eq.trans (congrArg Set.ncard (by ext e; induction e using Sym2.ind; exact Iff.rfl)) hM'k)
  by_cases hPuv : P.Adj u v
  swap
  · have hdown : ∀ {x y : Fin (2 * k + 6)}, P.Adj x y → (G.deleteEdges {s(u, v)}).Adj x y := by
      intro x y h
      rw [hG']
      refine ⟨P.adj_sub h, fun he => ?_⟩
      rcases hsym _ _ he with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact hPuv (hx ▸ hy ▸ h)
      · exact hPuv (hx ▸ hy ▸ h).symm
    exact ⟨⟨P.verts, P.Adj, hdown, P.edge_vert, P.symm⟩,
      SimpleGraph.Subgraph.isPerfectMatching_iff.mpr (fun x => hP' x), ⟨hMP.1, fun x y h => hMP.2 h⟩⟩
  have hmate : ∀ {x y z : Fin (2 * k + 6)}, P.Adj x y → P.Adj x z → y = z := fun {x y z} h1 h2 => (hP' x).unique h1 h2
  have hclos : ∀ {x y : Fin (2 * k + 6)}, P.Adj x y → x ∉ M'.verts → y ∉ M'.verts := by
    intro x y h hx hy
    obtain ⟨w, hw, -⟩ := hM' hy
    have hwx : w = x := hmate (hMPadj hw) h.symm
    subst hwx
    exact hx (M'.edge_vert hw.symm)
  have huM : u ∉ M'.verts := by
    intro hu'
    obtain ⟨w, hw, -⟩ := hM' hu'
    have hwv : w = v := hmate (hMPadj hw) hPuv
    subst hwv
    exact ((hG' _ _).mp (M'.adj_sub hw)).2 rfl
  have hvM : v ∉ M'.verts := hclos hPuv huM
  have n_u_v : u ≠ v := hGuv.ne
  obtain ⟨a, ha⟩ : ∃ a : Fin (2 * k + 6), a ∉ insert u (insert v SM) := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have h1 : insert u (insert v SM) = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    have h2 := Finset.card_insert_le u (insert v SM)
    have h3 := Finset.card_insert_le v SM
    rw [h1, Finset.card_univ, Fintype.card_fin] at h2
    omega
  simp only [Finset.mem_insert, not_or] at ha
  obtain ⟨hau, hav, haS⟩ := ha
  have n_u_a : u ≠ a := fun h => hau h.symm
  have n_v_a : v ≠ a := fun h => hav h.symm
  have haM : a ∉ M'.verts := fun h => haS (hSM a h)
  obtain ⟨b, hPab, -⟩ := hP' a
  have n_a_b : a ≠ b := (P.adj_sub hPab).ne
  have n_u_b : u ≠ b := fun h => n_v_a (hmate hPuv (h ▸ hPab.symm))
  have n_v_b : v ≠ b := fun h => n_u_a (hmate hPuv.symm (h ▸ hPab.symm))
  have hbM : b ∉ M'.verts := hclos hPab haM
  obtain ⟨c, hc⟩ : ∃ c : Fin (2 * k + 6), c ∉ insert u (insert v (insert a (insert b SM))) := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have h1 : insert u (insert v (insert a (insert b SM))) = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    have h2 := Finset.card_insert_le u (insert v (insert a (insert b SM)))
    have h3 := Finset.card_insert_le v (insert a (insert b SM))
    have h4 := Finset.card_insert_le a (insert b SM)
    have h5 := Finset.card_insert_le b SM
    rw [h1, Finset.card_univ, Fintype.card_fin] at h2
    omega
  simp only [Finset.mem_insert, not_or] at hc
  obtain ⟨hcu, hcv, hca, hcb, hcS⟩ := hc
  have n_u_c : u ≠ c := fun h => hcu h.symm
  have n_v_c : v ≠ c := fun h => hcv h.symm
  have n_a_c : a ≠ c := fun h => hca h.symm
  have n_b_c : b ≠ c := fun h => hcb h.symm
  have hcM : c ∉ M'.verts := fun h => hcS (hSM c h)
  obtain ⟨d, hPcd, -⟩ := hP' c
  have n_c_d : c ≠ d := (P.adj_sub hPcd).ne
  have n_u_d : u ≠ d := fun h => n_v_c (hmate hPuv (h ▸ hPcd.symm))
  have n_v_d : v ≠ d := fun h => n_u_c (hmate hPuv.symm (h ▸ hPcd.symm))
  have n_a_d : a ≠ d := fun h => n_b_c (hmate hPab (h ▸ hPcd.symm))
  have n_b_d : b ≠ d := fun h => n_a_c (hmate hPab.symm (h ▸ hPcd.symm))
  have hdM : d ∉ M'.verts := hclos hPcd hcM
  have hGab : G.Adj a b := P.adj_sub hPab
  have hGcd : G.Adj c d := P.adj_sub hPcd
  have tinj : Function.Injective (![u, v, a, b, c, d] : Fin 6 → Fin (2 * k + 6)) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    exacts [rfl, absurd hij n_u_v, absurd hij n_u_a, absurd hij n_u_b, absurd hij n_u_c, absurd hij n_u_d, absurd hij n_u_v.symm, rfl, absurd hij n_v_a, absurd hij n_v_b, absurd hij n_v_c, absurd hij n_v_d, absurd hij n_u_a.symm, absurd hij n_v_a.symm, rfl, absurd hij n_a_b, absurd hij n_a_c, absurd hij n_a_d, absurd hij n_u_b.symm, absurd hij n_v_b.symm, absurd hij n_a_b.symm, rfl, absurd hij n_b_c, absurd hij n_b_d, absurd hij n_u_c.symm, absurd hij n_v_c.symm, absurd hij n_a_c.symm, absurd hij n_b_c.symm, rfl, absurd hij n_c_d, absurd hij n_u_d.symm, absurd hij n_v_d.symm, absurd hij n_a_d.symm, absurd hij n_b_d.symm, absurd hij n_c_d.symm, rfl]
  have hPt : ∀ i, P.Adj ((![u, v, a, b, c, d] : Fin 6 → Fin (2 * k + 6)) i) ((![u, v, a, b, c, d] : Fin 6 → Fin (2 * k + 6)) ((![1, 0, 3, 2, 5, 4] : Fin 6 → Fin 6) i)) := by
    intro i; fin_cases i
    exacts [hPuv, hPuv.symm, hPab, hPab.symm, hPcd, hPcd.symm]
  have hTM : ∀ i, (![u, v, a, b, c, d] : Fin 6 → Fin (2 * k + 6)) i ∉ M'.verts := by
    intro i; fin_cases i
    exacts [huM, hvM, haM, hbM, hcM, hdM]
  have hTclos : ∀ i (w : Fin (2 * k + 6)), P.Adj ((![u, v, a, b, c, d] : Fin 6 → Fin (2 * k + 6)) i) w → w ∈ Set.range (![u, v, a, b, c, d] : Fin 6 → Fin (2 * k + 6)) :=
    fun i w h => ⟨(![1, 0, 3, 2, 5, 4] : Fin 6 → Fin 6) i, hmate (hPt i) h⟩
  have hre : ∀ τ : Fin 6 → Fin 6, (∀ i, τ (τ i) = i) → τ 0 ≠ 1 →
      (∀ i, G.Adj ((![u, v, a, b, c, d] : Fin 6 → Fin (2 * k + 6)) i) ((![u, v, a, b, c, d] : Fin 6 → Fin (2 * k + 6)) (τ i))) →
      ∃ P' : (G.deleteEdges {s(u, v)}).Subgraph, P'.IsPerfectMatching ∧ M' ≤ P' := by
    intro τ hinv h01 hτ
    refine ⟨⟨Set.univ, fun x y => (P.Adj x y ∧ x ∉ Set.range (![u, v, a, b, c, d] : Fin 6 → Fin (2 * k + 6)) ∧ y ∉ Set.range (![u, v, a, b, c, d] : Fin 6 → Fin (2 * k + 6))) ∨
        ∃ i, x = (![u, v, a, b, c, d] : Fin 6 → Fin (2 * k + 6)) i ∧ y = (![u, v, a, b, c, d] : Fin 6 → Fin (2 * k + 6)) (τ i), ?_, ?_, ?_⟩, ?_, ?_⟩
    · rintro x y (⟨h, hx, hy⟩ | ⟨i, rfl, rfl⟩)
      · rw [hG']
        refine ⟨P.adj_sub h, fun he => ?_⟩
        rcases hsym _ _ he with ⟨hxu, -⟩ | ⟨hxv, -⟩
        · exact hx ⟨0, hxu.symm⟩
        · exact hx ⟨1, hxv.symm⟩
      · rw [hG']
        refine ⟨hτ i, fun he => ?_⟩
        rcases hsym _ _ he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have e1 : i = 0 := tinj h1
          have e2 : τ i = 1 := tinj h2
          rw [e1] at e2
          exact h01 e2
        · have e1 : i = 1 := tinj h1
          have e2 : τ i = 0 := tinj h2
          rw [e1] at e2
          have e3 := hinv 1
          rw [e2] at e3
          exact h01 e3
    · intro x y _
      exact Set.mem_univ x
    · refine ⟨fun x y hxy => ?_⟩
      rcases hxy with ⟨h, hx, hy⟩ | ⟨i, rfl, rfl⟩
      · exact Or.inl ⟨h.symm, hy, hx⟩
      · exact Or.inr ⟨τ i, rfl, by rw [hinv i]⟩
    · rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
      intro x
      by_cases hx : x ∈ Set.range (![u, v, a, b, c, d] : Fin 6 → Fin (2 * k + 6))
      · obtain ⟨i, rfl⟩ := hx
        refine ⟨(![u, v, a, b, c, d] : Fin 6 → Fin (2 * k + 6)) (τ i), Or.inr ⟨i, rfl, rfl⟩, ?_⟩
        rintro w (⟨-, hx, -⟩ | ⟨j, hj, rfl⟩)
        · exact absurd ⟨i, rfl⟩ hx
        · rw [tinj hj]
      · obtain ⟨w, hw, huniq⟩ := hP' x
        have hwT : w ∉ Set.range (![u, v, a, b, c, d] : Fin 6 → Fin (2 * k + 6)) := by
          rintro ⟨i, rfl⟩
          exact hx (hTclos i x hw.symm)
        refine ⟨w, Or.inl ⟨hw, hx, hwT⟩, ?_⟩
        rintro w' (⟨h', -, -⟩ | ⟨j, hj, -⟩)
        · exact huniq w' h'
        · exact absurd ⟨j, hj.symm⟩ hx
    · refine ⟨fun x _ => Set.mem_univ x, fun x y h => Or.inl ⟨hMPadj h, ?_, ?_⟩⟩
      · rintro ⟨i, rfl⟩
        exact hTM i (M'.edge_vert h)
      · rintro ⟨i, rfl⟩
        exact hTM i (M'.edge_vert h.symm)
  rcases key (decide (u ≠ a ∧ ¬ G.Adj u a)) (decide (u ≠ b ∧ ¬ G.Adj u b)) (decide (u ≠ c ∧ ¬ G.Adj u c)) (decide (u ≠ d ∧ ¬ G.Adj u d)) (decide (v ≠ a ∧ ¬ G.Adj v a)) (decide (v ≠ b ∧ ¬ G.Adj v b)) (decide (v ≠ c ∧ ¬ G.Adj v c)) (decide (v ≠ d ∧ ¬ G.Adj v d)) (decide (a ≠ c ∧ ¬ G.Adj a c)) (decide (a ≠ d ∧ ¬ G.Adj a d)) (decide (b ≠ c ∧ ¬ G.Adj b c)) (decide (b ≠ d ∧ ¬ G.Adj b d))
    (fun h1 h2 => hnc a (of_decide_eq_true h1) (of_decide_eq_true h2))
    (fun h1 h2 => hnc b (of_decide_eq_true h1) (of_decide_eq_true h2))
    (fun h1 h2 => hnc c (of_decide_eq_true h1) (of_decide_eq_true h2))
    (fun h1 h2 => hnc d (of_decide_eq_true h1) (of_decide_eq_true h2))
    (fun h1 h2 h3 h4 h5 h6 h7 h8 => hnB ⟨a, b, c, d, n_a_b, n_c_d, of_decide_eq_true h1, of_decide_eq_true h2, of_decide_eq_true h3, of_decide_eq_true h4, Hsymm _ _ (of_decide_eq_true h5), Hsymm _ _ (of_decide_eq_true h7), Hsymm _ _ (of_decide_eq_true h6), Hsymm _ _ (of_decide_eq_true h8)⟩)
    (fun h1 h2 h3 h4 h5 h6 h7 h8 => hnB ⟨c, d, a, b, n_c_d, n_a_b, of_decide_eq_true h1, of_decide_eq_true h2, of_decide_eq_true h3, of_decide_eq_true h4, of_decide_eq_true h5, of_decide_eq_true h6, of_decide_eq_true h7, of_decide_eq_true h8⟩)
    (fun h1 h2 h3 h4 => hdeg u a b c d n_a_b n_a_c n_a_d n_b_c n_b_d n_c_d (of_decide_eq_true h1) (of_decide_eq_true h2) (of_decide_eq_true h3) (of_decide_eq_true h4))
    (fun h1 h2 h3 h4 => hdeg v a b c d n_a_b n_a_c n_a_d n_b_c n_b_d n_c_d (of_decide_eq_true h1) (of_decide_eq_true h2) (of_decide_eq_true h3) (of_decide_eq_true h4))
    (fun h1 h2 h3 h4 => hdeg a u v c d n_u_v n_u_c n_u_d n_v_c n_v_d n_c_d (Hsymm _ _ (of_decide_eq_true h1)) (Hsymm _ _ (of_decide_eq_true h2)) (of_decide_eq_true h3) (of_decide_eq_true h4))
    (fun h1 h2 h3 h4 => hdeg b u v c d n_u_v n_u_c n_u_d n_v_c n_v_d n_c_d (Hsymm _ _ (of_decide_eq_true h1)) (Hsymm _ _ (of_decide_eq_true h2)) (of_decide_eq_true h3) (of_decide_eq_true h4))
    (fun h1 h2 h3 h4 => hdeg c u v a b n_u_v n_u_a n_u_b n_v_a n_v_b n_a_b (Hsymm _ _ (of_decide_eq_true h1)) (Hsymm _ _ (of_decide_eq_true h2)) (Hsymm _ _ (of_decide_eq_true h3)) (Hsymm _ _ (of_decide_eq_true h4)))
    (fun h1 h2 h3 h4 => hdeg d u v a b n_u_v n_u_a n_u_b n_v_a n_v_b n_a_b (Hsymm _ _ (of_decide_eq_true h1)) (Hsymm _ _ (of_decide_eq_true h2)) (Hsymm _ _ (of_decide_eq_true h3)) (Hsymm _ _ (of_decide_eq_true h4))) with
    ⟨e02, e13⟩ | ⟨e02, e14, e35⟩ | ⟨e02, e15, e34⟩ | ⟨e03, e12⟩ | ⟨e03, e14, e25⟩ | ⟨e03, e15, e24⟩ | ⟨e04, e12, e35⟩ | ⟨e04, e13, e25⟩ | ⟨e04, e15⟩ | ⟨e05, e12, e34⟩ | ⟨e05, e13, e24⟩ | ⟨e05, e14⟩
  · exact hre ![2, 3, 0, 1, 5, 4] (by decide) (by decide) (by
      intro i; fin_cases i
      exacts [(hadj u a n_u_a e02), (hadj v b n_v_b e13), (hadj u a n_u_a e02).symm, (hadj v b n_v_b e13).symm, hGcd, hGcd.symm])
  · exact hre ![2, 4, 0, 5, 1, 3] (by decide) (by decide) (by
      intro i; fin_cases i
      exacts [(hadj u a n_u_a e02), (hadj v c n_v_c e14), (hadj u a n_u_a e02).symm, (hadj b d n_b_d e35), (hadj v c n_v_c e14).symm, (hadj b d n_b_d e35).symm])
  · exact hre ![2, 5, 0, 4, 3, 1] (by decide) (by decide) (by
      intro i; fin_cases i
      exacts [(hadj u a n_u_a e02), (hadj v d n_v_d e15), (hadj u a n_u_a e02).symm, (hadj b c n_b_c e34), (hadj b c n_b_c e34).symm, (hadj v d n_v_d e15).symm])
  · exact hre ![3, 2, 1, 0, 5, 4] (by decide) (by decide) (by
      intro i; fin_cases i
      exacts [(hadj u b n_u_b e03), (hadj v a n_v_a e12), (hadj v a n_v_a e12).symm, (hadj u b n_u_b e03).symm, hGcd, hGcd.symm])
  · exact hre ![3, 4, 5, 0, 1, 2] (by decide) (by decide) (by
      intro i; fin_cases i
      exacts [(hadj u b n_u_b e03), (hadj v c n_v_c e14), (hadj a d n_a_d e25), (hadj u b n_u_b e03).symm, (hadj v c n_v_c e14).symm, (hadj a d n_a_d e25).symm])
  · exact hre ![3, 5, 4, 0, 2, 1] (by decide) (by decide) (by
      intro i; fin_cases i
      exacts [(hadj u b n_u_b e03), (hadj v d n_v_d e15), (hadj a c n_a_c e24), (hadj u b n_u_b e03).symm, (hadj a c n_a_c e24).symm, (hadj v d n_v_d e15).symm])
  · exact hre ![4, 2, 1, 5, 0, 3] (by decide) (by decide) (by
      intro i; fin_cases i
      exacts [(hadj u c n_u_c e04), (hadj v a n_v_a e12), (hadj v a n_v_a e12).symm, (hadj b d n_b_d e35), (hadj u c n_u_c e04).symm, (hadj b d n_b_d e35).symm])
  · exact hre ![4, 3, 5, 1, 0, 2] (by decide) (by decide) (by
      intro i; fin_cases i
      exacts [(hadj u c n_u_c e04), (hadj v b n_v_b e13), (hadj a d n_a_d e25), (hadj v b n_v_b e13).symm, (hadj u c n_u_c e04).symm, (hadj a d n_a_d e25).symm])
  · exact hre ![4, 5, 3, 2, 0, 1] (by decide) (by decide) (by
      intro i; fin_cases i
      exacts [(hadj u c n_u_c e04), (hadj v d n_v_d e15), hGab, hGab.symm, (hadj u c n_u_c e04).symm, (hadj v d n_v_d e15).symm])
  · exact hre ![5, 2, 1, 4, 3, 0] (by decide) (by decide) (by
      intro i; fin_cases i
      exacts [(hadj u d n_u_d e05), (hadj v a n_v_a e12), (hadj v a n_v_a e12).symm, (hadj b c n_b_c e34), (hadj b c n_b_c e34).symm, (hadj u d n_u_d e05).symm])
  · exact hre ![5, 3, 4, 1, 2, 0] (by decide) (by decide) (by
      intro i; fin_cases i
      exacts [(hadj u d n_u_d e05), (hadj v b n_v_b e13), (hadj a c n_a_c e24), (hadj v b n_v_b e13).symm, (hadj a c n_a_c e24).symm, (hadj u d n_u_d e05).symm])
  · exact hre ![5, 4, 3, 2, 1, 0] (by decide) (by decide) (by
      intro i; fin_cases i
      exacts [(hadj u d n_u_d e05), (hadj v c n_v_c e14), hGab, hGab.symm, (hadj v c n_v_c e14).symm, (hadj u d n_u_d e05).symm])
