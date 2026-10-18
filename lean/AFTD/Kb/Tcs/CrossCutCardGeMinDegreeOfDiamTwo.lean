import AFTD.Prelude
import AFTD.Kb.Tcs.CrossingPairsCardEqCrossingEdgesCard
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cross_cut_card_ge_minDegree_of_diam_two

Topic: graphs   Node: 2724056066c7

Provenance: helper lemma. step towards edge_connectivity_ge_min_degree_mul_lly_lower_bound_two

Plesník's cut lemma: in a finite connected graph G with diam(G) = 2, every nontrivial vertex cut (A, Aᶜ) has at least δ(G) crossing edges.
-/

lemma cross_cut_card_ge_minDegree_of_diam_two_symm {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    (G.edgeFinset.filter (fun e => ∃ u ∈ (Aᶜ : Finset V), ∃ v ∈ (Aᶜᶜ : Finset V), e = s(u, v))).card =
      (G.edgeFinset.filter (fun e => ∃ u ∈ A, ∃ v ∈ (Aᶜ : Finset V), e = s(u, v))).card := by
  congr 1
  simp only [compl_compl]
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨he, u, hu, v, hv, rfl⟩
    exact ⟨he, v, hv, u, hu, Sym2.eq_swap⟩
  · rintro ⟨he, u, hu, v, hv, rfl⟩
    exact ⟨he, v, hv, u, hu, Sym2.eq_swap⟩

lemma cross_cut_card_ge_minDegree_of_diam_two_sum {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    ((A ×ˢ (Aᶜ : Finset V)).filter (fun p : V × V => G.Adj p.1 p.2)).card =
      ∑ b ∈ (Aᶜ : Finset V), (A.filter (fun a => G.Adj a b)).card := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product_right]
  congr 1
  ext b
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

lemma cross_cut_card_ge_minDegree_of_diam_two_deg {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (b : V) :
    G.degree b = ((G.neighborFinset b).filter (fun a => a ∈ (Aᶜ : Finset V))).card +
      (A.filter (fun a => G.Adj a b)).card := by
  have h : (G.neighborFinset b).filter (fun a => ¬ a ∈ (Aᶜ : Finset V)) = A.filter (fun a => G.Adj a b) := by
    ext a
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, Finset.mem_compl]
    rw [G.adj_comm]
    tauto
  show (G.neighborFinset b).card = _
  rw [← h]
  exact (Finset.card_filter_add_card_filter_not (fun a => a ∈ (Aᶜ : Finset V))).symm

lemma cross_cut_card_ge_minDegree_of_diam_two_sub {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (b : V) (hb : b ∈ (Aᶜ : Finset V)) :
    ((G.neighborFinset b).filter (fun a => a ∈ (Aᶜ : Finset V))).card ≤ (Aᶜ : Finset V).card - 1 := by
  have h_sub : (G.neighborFinset b).filter (fun a => a ∈ (Aᶜ : Finset V)) ⊆ (Aᶜ : Finset V).erase b := by
    intro a ha
    rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at ha
    rw [Finset.mem_erase]
    exact ⟨fun h => G.irrefl (h ▸ ha.1), ha.2⟩
  have h_card := Finset.card_le_card h_sub
  rw [Finset.card_erase_of_mem hb] at h_card
  exact h_card

lemma cross_cut_card_ge_minDegree_of_diam_two_of_ge1 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (hAc : (Aᶜ : Finset V).Nonempty)
    (h_ge1 : ∀ b ∈ (Aᶜ : Finset V), 1 ≤ (A.filter (fun v => G.Adj v b)).card) :
    G.minDegree ≤ (G.edgeFinset.filter (fun e => ∃ u ∈ A, ∃ v ∈ (Aᶜ : Finset V), e = s(u, v))).card := by
  rw [← crossing_pairs_card_eq_crossing_edges_card, cross_cut_card_ge_minDegree_of_diam_two_sum]
  by_cases h_card : G.minDegree ≤ (Aᶜ : Finset V).card
  · have h_sum : (Aᶜ : Finset V).card ≤ ∑ b ∈ (Aᶜ : Finset V), (A.filter (fun v => G.Adj v b)).card := by
      have : ∑ b ∈ (Aᶜ : Finset V), 1 ≤ ∑ b ∈ (Aᶜ : Finset V), (A.filter (fun v => G.Adj v b)).card :=
        Finset.sum_le_sum (fun b hb => h_ge1 b hb)
      simpa using this
    omega
  · have h_le : (Aᶜ : Finset V).card ≤ G.minDegree := by omega
    have h_pos : 1 ≤ (Aᶜ : Finset V).card := hAc.card_pos
    have h_each : ∀ b ∈ (Aᶜ : Finset V), G.minDegree + 1 - (Aᶜ : Finset V).card ≤ (A.filter (fun v => G.Adj v b)).card := by
      intro b hb
      have h1 := G.minDegree_le_degree b
      rw [cross_cut_card_ge_minDegree_of_diam_two_deg G A b] at h1
      have h2 := cross_cut_card_ge_minDegree_of_diam_two_sub G A b hb
      omega
    have h_sum : ∑ b ∈ (Aᶜ : Finset V), (G.minDegree + 1 - (Aᶜ : Finset V).card) ≤ ∑ b ∈ (Aᶜ : Finset V), (A.filter (fun v => G.Adj v b)).card :=
      Finset.sum_le_sum (fun b hb => h_each b hb)
    rw [Finset.sum_const_nat (fun _ _ => rfl)] at h_sum
    have h_ineq : G.minDegree ≤ (Aᶜ : Finset V).card * (G.minDegree + 1 - (Aᶜ : Finset V).card) := by
      have h_rew : G.minDegree + 1 - (Aᶜ : Finset V).card = G.minDegree - (Aᶜ : Finset V).card + 1 := by omega
      rw [h_rew]
      zify [h_le]
      have h1 : 0 ≤ ((Aᶜ : Finset V).card : ℤ) - 1 := by omega
      have h2 : 0 ≤ (G.minDegree : ℤ) - (Aᶜ : Finset V).card := by omega
      have h3 : 0 ≤ (((Aᶜ : Finset V).card : ℤ) - 1) * ((G.minDegree : ℤ) - (Aᶜ : Finset V).card) := mul_nonneg h1 h2
      nlinarith
    omega

lemma cross_cut_card_ge_minDegree_of_diam_two_local {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (hd : G.diam = 2)
    (A : Finset V) (a b : V) (ha : a ∈ A) (hb : b ∈ (Aᶜ : Finset V)) :
    1 ≤ (Aᶜ.filter (G.Adj a ·)).card + (A.filter (fun v => G.Adj v b)).card := by
  have hediam : G.ediam ≠ ⊤ := by
    intro h
    have : G.diam = 0 := SimpleGraph.diam_eq_zero_of_ediam_eq_top h
    omega
  by_cases hab : G.Adj a b
  · have h1 : b ∈ Aᶜ.filter (G.Adj a ·) := by
      rw [Finset.mem_filter]
      exact ⟨hb, hab⟩
    have : 1 ≤ (Aᶜ.filter (G.Adj a ·)).card := Finset.card_pos.mpr ⟨b, h1⟩
    omega
  · have hne : a ≠ b := by
      rintro rfl
      have : a ∈ A ∧ a ∈ Aᶜ := ⟨ha, hb⟩
      simp at this
    have hle : G.dist a b ≤ 2 := by
      have := SimpleGraph.dist_le_diam hediam (u := a) (v := b)
      omega
    have hpos : 0 < G.dist a b := hG.pos_dist_of_ne hne
    have hne1 : G.dist a b ≠ 1 := by
      intro h1
      have := (SimpleGraph.dist_eq_one_iff_adj.mp h1)
      contradiction
    have hdist2 : G.dist a b = 2 := by omega
    obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist a b
    rw [hdist2] at hp
    have ⟨c, hac, hcb⟩ : ∃ c : V, G.Adj a c ∧ G.Adj c b := by
      cases p with
      | nil => simp [SimpleGraph.Walk.length_nil] at hp
      | cons hac p' =>
        cases p' with
        | nil => simp [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hp
        | cons hcb p'' =>
          cases p'' with
          | nil => exact ⟨_, hac, hcb⟩
          | cons _ _ =>
            simp only [SimpleGraph.Walk.length_cons] at hp
            omega
    by_cases hc : c ∈ A
    · have h1 : c ∈ A.filter (fun v => G.Adj v b) := by
        rw [Finset.mem_filter]
        exact ⟨hc, hcb⟩
      have : 1 ≤ (A.filter (fun v => G.Adj v b)).card := Finset.card_pos.mpr ⟨c, h1⟩
      omega
    · have hc' : c ∈ (Aᶜ : Finset V) := by
        rw [Finset.mem_compl]
        exact hc
      have h1 : c ∈ Aᶜ.filter (G.Adj a ·) := by
        rw [Finset.mem_filter]
        exact ⟨hc', hac⟩
      have : 1 ≤ (Aᶜ.filter (G.Adj a ·)).card := Finset.card_pos.mpr ⟨c, h1⟩
      omega

/-- In a diameter-2 graph every nontrivial cut carries at least δ(G) edges. -/
theorem cross_cut_card_ge_minDegree_of_diam_two {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (hd : G.diam = 2)
    (A : Finset V) (hA : A.Nonempty) (hAc : (Aᶜ : Finset V).Nonempty) :
    G.minDegree ≤ (G.edgeFinset.filter (fun e => ∃ u ∈ A, ∃ v ∈ (Aᶜ : Finset V), e = s(u, v))).card := by
  by_cases h : ∃ b ∈ (Aᶜ : Finset V), (A.filter (fun v => G.Adj v b)).card = 0
  · obtain ⟨b, hb, hb0⟩ := h
    have h_ge1 : ∀ a ∈ A, 1 ≤ (Aᶜ.filter (G.Adj a ·)).card := by
      intro a ha
      have h_loc := cross_cut_card_ge_minDegree_of_diam_two_local G hG hd A a b ha hb
      omega
    have h_ge1' : ∀ a ∈ (Aᶜᶜ : Finset V), 1 ≤ ((Aᶜ : Finset V).filter (fun v => G.Adj v a)).card := by
      simp only [compl_compl]
      intro a ha
      have h := h_ge1 a ha
      have heq : Aᶜ.filter (G.Adj a ·) = (Aᶜ : Finset V).filter (fun v => G.Adj v a) := by
        ext v
        simp only [Finset.mem_filter]
        rw [G.adj_comm]
      rw [heq] at h
      exact h
    have h_step := cross_cut_card_ge_minDegree_of_diam_two_of_ge1 G (Aᶜ : Finset V) (by simp [compl_compl, hA]) h_ge1'
    rw [cross_cut_card_ge_minDegree_of_diam_two_symm] at h_step
    exact h_step
  · have h_ge1 : ∀ b ∈ (Aᶜ : Finset V), 1 ≤ (A.filter (fun v => G.Adj v b)).card := by
      intro b hb
      by_contra hc
      have : (A.filter (fun v => G.Adj v b)).card = 0 := by omega
      exact h ⟨b, hb, this⟩
    exact cross_cut_card_ge_minDegree_of_diam_two_of_ge1 G A hAc h_ge1
