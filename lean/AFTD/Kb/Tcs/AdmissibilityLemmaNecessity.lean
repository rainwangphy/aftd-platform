import AFTD.Prelude
import AFTD.Kb.Tcs.IsTotalEdgeIrregularLabeling
import AFTD.Kb.Tcs.SimpleGraphEndpointSumEdges

/-!
# admissibility_lemma_necessity

Topic: graphs   Node: 391eb9b54b31

Provenance: helper lemma. arXiv:2611.16338, Lemma 2.1

Let s ≥ 3, let G be a finite simple graph, and let φ : V → ℕ be a vertex labeling such that φ(v) ∈ {1, s} for all v. Let a = |E_2|, b = |E_{s+1}|, and c = |E_{2s}| be the counts of edges with endpoint label sums 2, s + 1, and 2s, respectively. If φ extends to a total edge irregular s-labeling of G, then a ≤ s, b ≤ s, c ≤ s, a + b ≤ 2s - 1, b + c ≤ 2s - 1, and a + b + c ≤ 3s - 2.
-/

open scoped Classical in
/-- Necessity direction of the admissibility lemma for binary vertex labelings. -/
theorem admissibility_lemma_necessity {V : Type*} [Fintype V]
    (G : SimpleGraph V) (s : ℕ) (hs : 3 ≤ s) (φ : V → ℕ)
    (hφ : ∀ v : V, φ v = 1 ∨ φ v = s)
    (h_ext : ∃ ψ : G.edgeSet → ℕ, is_total_edge_irregular_labeling G s φ ψ) :
    let a := (simple_graph_endpoint_sum_edges G φ 2).card
    let b := (simple_graph_endpoint_sum_edges G φ (s + 1)).card
    let c := (simple_graph_endpoint_sum_edges G φ (2 * s)).card
    a ≤ s ∧ b ≤ s ∧ c ≤ s ∧ a + b ≤ 2 * s - 1 ∧ b + c ≤ 2 * s - 1 ∧ a + b + c ≤ 3 * s - 2 := by
  obtain ⟨ψ, hψ⟩ := h_ext
  simp only [is_total_edge_irregular_labeling] at hψ
  obtain ⟨hφb, hψb, hinj⟩ := hψ
  let L : Sym2 V → ℕ := Sym2.lift ⟨fun u v => φ u + φ v, fun a b => Nat.add_comm _ _⟩
  let f : Sym2 V → ℕ := fun e => if h : e ∈ G.edgeSet then L e + ψ ⟨e, h⟩ else 0
  have hinjf : Set.InjOn f (G.edgeSet : Set (Sym2 V)) := by
    intro e1 he1 e2 he2 heq
    have h1 : f e1 = L e1 + ψ ⟨e1, he1⟩ := dif_pos he1
    have h2 : f e2 = L e2 + ψ ⟨e2, he2⟩ := dif_pos he2
    rw [h1, h2] at heq
    have hinj' := hinj ⟨e1, he1⟩ ⟨e2, he2⟩ heq
    exact congrArg Subtype.val hinj'
  have hmem : ∀ (r : ℕ) (e : Sym2 V), e ∈ simple_graph_endpoint_sum_edges G φ r → e ∈ G.edgeSet := by
    intro r e he
    simp only [simple_graph_endpoint_sum_edges, Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
    exact he.1
  have hLval : ∀ (r : ℕ) (e : Sym2 V), e ∈ simple_graph_endpoint_sum_edges G φ r → L e = r := by
    intro r e he
    simp only [simple_graph_endpoint_sum_edges, Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
    exact he.2
  have hbdd : ∀ (r : ℕ) (e : Sym2 V), e ∈ simple_graph_endpoint_sum_edges G φ r →
      r + 1 ≤ f e ∧ f e ≤ r + s := by
    intro r e he
    have hee : e ∈ G.edgeSet := hmem r e he
    have hLe : L e = r := hLval r e he
    have hfe : f e = L e + ψ ⟨e, hee⟩ := dif_pos hee
    obtain ⟨h1, h2⟩ := hψb ⟨e, hee⟩
    rw [hfe, hLe]
    exact ⟨by omega, by omega⟩
  have key2 : ∀ (lo hi : ℕ) (S : Finset (Sym2 V)),
      (∀ e ∈ S, e ∈ G.edgeSet) →
      (∀ e ∈ S, lo ≤ f e ∧ f e ≤ hi) →
      S.card ≤ hi + 1 - lo := by
    intro lo hi S hmemS hbound
    calc S.card ≤ (Finset.Icc lo hi).card := by
          apply Finset.card_le_card_of_injOn f
          · intro e he
            simp only [Finset.mem_coe, Finset.mem_Icc]
            exact hbound e (Finset.mem_coe.mp he)
          · intro e1 he1 e2 he2 heq
            exact hinjf (hmemS e1 (Finset.mem_coe.mp he1)) (hmemS e2 (Finset.mem_coe.mp he2)) heq
      _ = hi + 1 - lo := Nat.card_Icc lo hi
  set A := simple_graph_endpoint_sum_edges G φ 2 with hA
  set B := simple_graph_endpoint_sum_edges G φ (s + 1) with hB
  set C := simple_graph_endpoint_sum_edges G φ (2 * s) with hC
  have hA_bdd : ∀ e ∈ A, 3 ≤ f e ∧ f e ≤ s + 2 := by
    intro e he
    have := hbdd 2 e (hA ▸ he)
    omega
  have hB_bdd : ∀ e ∈ B, s + 2 ≤ f e ∧ f e ≤ 2 * s + 1 := by
    intro e he
    have := hbdd (s + 1) e (hB ▸ he)
    omega
  have hC_bdd : ∀ e ∈ C, 2 * s + 1 ≤ f e ∧ f e ≤ 3 * s := by
    intro e he
    have := hbdd (2 * s) e (hC ▸ he)
    omega
  have hA_mem : ∀ e ∈ A, e ∈ G.edgeSet := fun e he => hmem 2 e (hA ▸ he)
  have hB_mem : ∀ e ∈ B, e ∈ G.edgeSet := fun e he => hmem (s + 1) e (hB ▸ he)
  have hC_mem : ∀ e ∈ C, e ∈ G.edgeSet := fun e he => hmem (2 * s) e (hC ▸ he)
  have hAB_disj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro e heA heB
    have h1 : L e = 2 := hLval 2 e (hA ▸ heA)
    have h2 : L e = s + 1 := hLval (s + 1) e (hB ▸ heB)
    omega
  have hBC_disj : Disjoint B C := by
    rw [Finset.disjoint_left]
    intro e heB heC
    have h1 : L e = s + 1 := hLval (s + 1) e (hB ▸ heB)
    have h2 : L e = 2 * s := hLval (2 * s) e (hC ▸ heC)
    omega
  have hAC_disj : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro e heA heC
    have h1 : L e = 2 := hLval 2 e (hA ▸ heA)
    have h2 : L e = 2 * s := hLval (2 * s) e (hC ▸ heC)
    omega
  have hABC_disj : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_union_left]
    exact ⟨hAC_disj, hBC_disj⟩
  have hA_card : A.card ≤ s := by
    have := key2 3 (s + 2) A hA_mem hA_bdd
    omega
  have hB_card : B.card ≤ s := by
    have := key2 (s + 2) (2 * s + 1) B hB_mem hB_bdd
    omega
  have hC_card : C.card ≤ s := by
    have := key2 (2 * s + 1) (3 * s) C hC_mem hC_bdd
    omega
  have hAB_bdd : ∀ e ∈ A ∪ B, 3 ≤ f e ∧ f e ≤ 2 * s + 1 := by
    intro e he
    rw [Finset.mem_union] at he
    rcases he with heA | heB
    · have := hA_bdd e heA; omega
    · have := hB_bdd e heB; omega
  have hAB_mem : ∀ e ∈ A ∪ B, e ∈ G.edgeSet := by
    intro e he
    rw [Finset.mem_union] at he
    exact he.elim (hA_mem e) (hB_mem e)
  have hAB_card : (A ∪ B).card ≤ 2 * s - 1 := by
    have := key2 3 (2 * s + 1) (A ∪ B) hAB_mem hAB_bdd
    omega
  have hBC_bdd : ∀ e ∈ B ∪ C, s + 2 ≤ f e ∧ f e ≤ 3 * s := by
    intro e he
    rw [Finset.mem_union] at he
    rcases he with heB | heC
    · have := hB_bdd e heB; omega
    · have := hC_bdd e heC; omega
  have hBC_mem : ∀ e ∈ B ∪ C, e ∈ G.edgeSet := by
    intro e he
    rw [Finset.mem_union] at he
    exact he.elim (hB_mem e) (hC_mem e)
  have hBC_card : (B ∪ C).card ≤ 2 * s - 1 := by
    have := key2 (s + 2) (3 * s) (B ∪ C) hBC_mem hBC_bdd
    omega
  have hABC_bdd : ∀ e ∈ A ∪ B ∪ C, 3 ≤ f e ∧ f e ≤ 3 * s := by
    intro e he
    rw [Finset.mem_union] at he
    rcases he with heAB | heC
    · have := hAB_bdd e heAB; omega
    · have := hC_bdd e heC; omega
  have hABC_mem : ∀ e ∈ A ∪ B ∪ C, e ∈ G.edgeSet := by
    intro e he
    rw [Finset.mem_union] at he
    exact he.elim (hAB_mem e) (hC_mem e)
  have hABC_card : (A ∪ B ∪ C).card ≤ 3 * s - 2 := by
    have := key2 3 (3 * s) (A ∪ B ∪ C) hABC_mem hABC_bdd
    omega
  dsimp only
  refine ⟨hA_card, hB_card, hC_card, ?_, ?_, ?_⟩
  · rw [← Finset.card_union_of_disjoint hAB_disj]; exact hAB_card
  · rw [← Finset.card_union_of_disjoint hBC_disj]; exact hBC_card
  · have hcab : (A ∪ B ∪ C).card = A.card + B.card + C.card := by
      rw [Finset.card_union_of_disjoint hABC_disj, Finset.card_union_of_disjoint hAB_disj]
    rw [← hcab]; exact hABC_card
