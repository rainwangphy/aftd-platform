import AFTD.Prelude
import AFTD.Kb.Tcs.HypercubeGraph
import AFTD.Kb.Tcs.C4FreeHypercubeThreeFaceStarRootsCardLeOne

/-!
# c4_free_hypercube_parity_star_sum_le

Topic: graphs   Node: 67c078524f3d

Provenance: formalization of a published result. Source: arXiv:2611.27284 (The four-cycle extremal number of the seven-cube), Lemma 2.2 (star capacity), the consequence S_P(G) ≤ C(n,3) 2^(n−3).

Let n ≥ 3 and let G be a subgraph of the n-dimensional hypercube Q_n (vertices {0,1}^n, adjacent at Hamming distance 1) containing no copy of the 4-cycle C_4. For a parity side P (the vertices whose number of coordinates equal to 1 has a given parity p ∈ {0,1}), the sum over v in P of C(d_G(v), 3) is at most C(n,3)·2^(n−3).
-/

theorem c4hf_adj_eq_flip {n : ℕ} (v u : Fin n → Bool) (h : (hypercube_graph n).Adj v u) :
    ∃ l, u = c4hf_flip v l := by
  have h1 : hammingDist v u = 1 := h
  unfold hammingDist at h1
  obtain ⟨l, hl⟩ := Finset.card_eq_one.1 h1
  refine ⟨l, funext fun m => ?_⟩
  have hm := Finset.ext_iff.1 hl m
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hm
  simp only [c4hf_flip]
  by_cases hml : m = l
  · rw [if_pos hml]
    have := hm.2 hml
    cases hv : v m <;> cases hu : u m <;> simp_all
  · rw [if_neg hml]
    have := mt hm.1 hml
    simp only [ne_eq, not_not] at this
    exact this.symm

theorem c4hf_flip_injective {n : ℕ} (v : Fin n → Bool) : Function.Injective (c4hf_flip v) := by
  intro l l' h
  by_contra hne
  have := congrFun h l
  simp [c4hf_flip, hne] at this

open Classical in
theorem c4hf_degree_eq {n : ℕ} (G : SimpleGraph (Fin n → Bool)) (hG : G ≤ hypercube_graph n)
    (v : Fin n → Bool) :
    G.degree v = (Finset.univ.filter fun l => G.Adj v (c4hf_flip v l)).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have : G.neighborFinset v =
      (Finset.univ.filter fun l => G.Adj v (c4hf_flip v l)).image (c4hf_flip v) := by
    ext u
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro h
      obtain ⟨l, rfl⟩ := c4hf_adj_eq_flip v u (hG h)
      exact ⟨l, h, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact hl
  rw [this, Finset.card_image_of_injective _ (c4hf_flip_injective v)]

open Classical in
theorem c4_free_hypercube_parity_star_sum_le (n : ℕ) (hn : 3 ≤ n)
    (G : SimpleGraph (Fin n → Bool)) (hG : G ≤ hypercube_graph n)
    (hC4 : (SimpleGraph.cycleGraph 4).Free G) (p : ℕ) (hp : p < 2) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin n → Bool =>
        (Finset.univ.filter fun l => v l = true).card % 2 = p),
      (G.degree v).choose 3 ≤ n.choose 3 * 2 ^ (n - 3) := by
  have hX : ∑ v ∈ Finset.univ.filter (fun v : Fin n → Bool =>
        (Finset.univ.filter fun l => v l = true).card % 2 = p), (G.degree v).choose 3 =
      ((Finset.univ.filter (fun v : Fin n → Bool =>
        (Finset.univ.filter fun l => v l = true).card % 2 = p)).sigma fun v =>
          (Finset.univ.filter fun l => G.Adj v (c4hf_flip v l)).powersetCard 3).card := by
    rw [Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.card_powersetCard, c4hf_degree_eq G hG v]
  have hT : ((Finset.univ.powersetCard 3 : Finset (Finset (Fin n))).sigma fun D =>
      Finset.univ.filter fun u : Fin n → Bool => ∀ l ∈ D, u l = false).card ≤
        n.choose 3 * 2 ^ (n - 3) := by
    rw [Finset.card_sigma]
    calc _ ≤ ∑ D ∈ (Finset.univ.powersetCard 3 : Finset (Finset (Fin n))), 2 ^ (n - 3) := by
          apply Finset.sum_le_sum
          intro D hD
          have hD3 : D.card = 3 := (Finset.mem_powersetCard.1 hD).2
          calc _ ≤ (Dᶜ).powerset.card := by
                apply Finset.card_le_card_of_injOn
                  (fun u : Fin n → Bool => Finset.univ.filter fun l => u l = true)
                · intro u hu
                  simp only [Finset.coe_filter, Finset.mem_univ, true_and,
                    Set.mem_ofPred_eq] at hu
                  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
                    Finset.coe_subset]
                  intro l hl
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
                  rw [Finset.mem_compl]
                  intro hlD
                  rw [hu l hlD] at hl
                  exact Bool.false_ne_true hl
                · intro u _ u' _ h
                  funext l
                  have := Finset.ext_iff.1 h l
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
                  cases hu : u l <;> cases hu' : u' l <;> simp_all
            _ = 2 ^ (n - 3) := by
                rw [Finset.card_powerset, Finset.card_compl, Fintype.card_fin, hD3]
      _ = _ := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]
  rw [hX]
  refine le_trans (Finset.card_le_card_of_injOn
    (fun x => (⟨x.2, fun l => if l ∈ x.2 then false else x.1 l⟩ :
      Σ _ : Finset (Fin n), Fin n → Bool)) ?_ ?_) hT
  · rintro ⟨v, D⟩ hx
    rw [Finset.mem_coe, Finset.mem_sigma] at hx
    rw [Finset.mem_coe, Finset.mem_sigma]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, (Finset.mem_powersetCard.1 hx.2).2⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro l hl
      simp [hl]
  · rintro ⟨v, D⟩ hx ⟨v', D'⟩ hy hxy
    rw [Finset.mem_coe, Finset.mem_sigma] at hx hy
    dsimp only at hx hy
    simp only [Sigma.mk.injEq] at hxy
    obtain ⟨hDD, hbase⟩ := hxy
    subst hDD
    have hbase' := eq_of_heq hbase
    have hagree : ∀ l, l ∉ D → v' l = v l := by
      intro l hl
      have := congrFun hbase' l
      simp only [if_neg hl] at this
      exact this.symm
    obtain ⟨hvP, hvD⟩ := hx
    obtain ⟨hv'P, hv'D⟩ := hy
    rw [Finset.mem_powersetCard] at hvD hv'D
    obtain ⟨i, j, k, hij, hik, hjk, hD⟩ := Finset.card_eq_three.1 hvD.2
    have hmemD : ∀ l, l ∈ D ↔ (l = i ∨ l = j ∨ l = k) := by
      intro l; rw [hD]; simp
    have hroot : ∀ x : Fin n → Bool, D ⊆ Finset.univ.filter (fun l => G.Adj x (c4hf_flip x l)) →
        (∀ l, l ∉ D → x l = v l) →
        ∀ u : Fin n → Bool, (∀ l, l ≠ i → l ≠ j → l ≠ k → u l = v l) →
          (hypercube_graph n).Adj x u → G.Adj x u := by
      intro x hxD hxv u hu hadj
      obtain ⟨l, rfl⟩ := c4hf_adj_eq_flip x u hadj
      have hl : l ∈ D := by
        by_contra hl
        have h1 := (hmemD l).not.1 hl
        push_neg at h1
        have := hu l h1.1 h1.2.1 h1.2.2
        rw [← hxv l hl] at this
        simp [c4hf_flip] at this
      have := hxD hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    have hcard := c4_free_hypercube_three_face_star_roots_card_le_one n G hG hC4 p i j k
      hij hik hjk v
    have hnotD : ∀ l, l ≠ i → l ≠ j → l ≠ k → l ∉ D := by
      intro l h1 h2 h3 hl
      rcases (hmemD l).1 hl with h | h | h <;> contradiction
    have hv_in : v ∈ (Finset.univ.filter fun u : Fin n → Bool =>
        (∀ l, l ≠ i → l ≠ j → l ≠ k → u l = v l) ∧
        (Finset.univ.filter fun l => u l = true).card % 2 = p ∧
        ∀ u' : Fin n → Bool, (∀ l, l ≠ i → l ≠ j → l ≠ k → u' l = v l) →
          (hypercube_graph n).Adj u u' → G.Adj u u') := by
      rw [Finset.mem_filter] at hvP ⊢
      exact ⟨Finset.mem_univ _, fun _ _ _ _ => rfl, hvP.2, hroot v hvD.1 (fun _ _ => rfl)⟩
    have hv'_in : v' ∈ (Finset.univ.filter fun u : Fin n → Bool =>
        (∀ l, l ≠ i → l ≠ j → l ≠ k → u l = v l) ∧
        (Finset.univ.filter fun l => u l = true).card % 2 = p ∧
        ∀ u' : Fin n → Bool, (∀ l, l ≠ i → l ≠ j → l ≠ k → u' l = v l) →
          (hypercube_graph n).Adj u u' → G.Adj u u') := by
      rw [Finset.mem_filter] at hv'P ⊢
      exact ⟨Finset.mem_univ _, fun l h1 h2 h3 => hagree l (hnotD l h1 h2 h3), hv'P.2,
        hroot v' hv'D.1 hagree⟩
    have := Finset.card_le_one.1 hcard v hv_in v' hv'_in
    subst this
    rfl
