import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# connected_cubic_bipartite_has_no_cut_vertex

Topic: graphs   Node: 72dccb3b48fa

Provenance: formalization of a published result. Source: arXiv:2611.16649 Sec. 3.4, p. 10

Every finite connected cubic bipartite graph has no cut vertex: deleting any single vertex leaves a preconnected induced subgraph.
-/

private lemma connected_cubic_bipartite_has_no_cut_vertex_fin2_eq_of_ne_of_ne {a b c : Fin 2}
    (h1 : a ≠ c) (h2 : b ≠ c) : a = b := by
  revert a b c
  decide

private lemma connected_cubic_bipartite_has_no_cut_vertex_exists_adj_of_connected
    {V : Type*} (G : SimpleGraph V) (hconn : G.Connected)
    (S : Set V) {u : V} (hu : u ∈ S) {w : V} (hw : w ∉ S) :
    ∃ a ∈ S, ∃ b ∉ S, G.Adj a b := by
  obtain ⟨p⟩ := hconn.preconnected u w
  obtain ⟨d, _, h1, h2⟩ := p.exists_boundary_dart S hu hw
  exact ⟨d.toProd.1, h1, d.toProd.2, h2, d.adj⟩

private lemma connected_cubic_bipartite_has_no_cut_vertex_sum_bipartite_edges
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A1 B1 : Finset V) :
    ∑ u ∈ A1, (B1.filter (G.Adj u)).card = ∑ w ∈ B1, (A1.filter (G.Adj w)).card := by
  have h1 : ∀ u, (B1.filter (G.Adj u)).card = ∑ w ∈ B1, (if G.Adj u w then 1 else 0) := by
    intro u
    rw [Finset.card_filter]
  have h2 : ∀ w, (A1.filter (G.Adj w)).card = ∑ u ∈ A1, (if G.Adj u w then 1 else 0) := by
    intro w
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro u _
    by_cases h : G.Adj u w
    · rw [if_pos h, if_pos (G.adj_symm h)]
    · rw [if_neg h, if_neg (fun h' => h (G.adj_symm h'))]
  simp_rw [h1, h2]
  exact Finset.sum_comm

/-- Every connected cubic bipartite graph has no cut vertex: deleting any single vertex leaves a preconnected induced subgraph. -/
theorem connected_cubic_bipartite_has_no_cut_vertex
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hreg : G.IsRegularOfDegree 3) (hbip : G.IsBipartite)
    (v : V) : (G.induce {v}ᶜ).Preconnected := by
  classical
  rw [SimpleGraph.Preconnected]
  by_contra! hnot
  obtain ⟨x, y, hxy⟩ := hnot
  obtain ⟨c⟩ := hbip
  let H := G.induce {v}ᶜ
  let C1 : Finset V := Finset.univ.filter (fun u => ∃ h : u ∈ ({v}ᶜ : Set V), H.Reachable x ⟨u, h⟩)
  have hC1_eq : C1 = Finset.univ.filter (fun u => ∃ h : u ∈ ({v}ᶜ : Set V), H.Reachable x ⟨u, h⟩) := rfl
  have hx : x.1 ∈ C1 := by
    rw [hC1_eq, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, x.2, ?_⟩
    have : (⟨x.1, x.2⟩ : {w : V // w ∈ ({v}ᶜ : Set V)}) = x := Subtype.ext rfl
    rw [this]
  have hy : y.1 ∉ C1 := by
    rw [hC1_eq, Finset.mem_filter]
    rintro ⟨-, h, hr⟩
    have : (⟨y.1, h⟩ : {w : V // w ∈ ({v}ᶜ : Set V)}) = y := Subtype.ext rfl
    rw [this] at hr
    exact hxy hr
  have hv : v ∉ C1 := by
    rw [hC1_eq, Finset.mem_filter]
    rintro ⟨-, h, -⟩
    exact h rfl
  have hadj : ∀ {u w}, u ∈ C1 → G.Adj u w → w ∈ C1 ∨ w = v := by
    intro u w hu hadj
    by_cases hw : w = v
    · exact Or.inr hw
    · left
      rw [hC1_eq, Finset.mem_filter] at hu ⊢
      obtain ⟨-, hu_ne, hr⟩ := hu
      have hw_mem : w ∈ ({v}ᶜ : Set V) := hw
      refine ⟨Finset.mem_univ _, hw_mem, ?_⟩
      have hadjH : H.Adj ⟨u, hu_ne⟩ ⟨w, hw_mem⟩ := by
        rw [SimpleGraph.induce_adj]
        exact hadj
      exact hr.trans hadjH.reachable
  let A1 := C1.filter (fun u => c u = c v)
  let B1 := C1.filter (fun u => c u ≠ c v)
  have hB1_eq : B1 = C1.filter (fun u => c u ≠ c v) := rfl
  have h_A1_deg : ∀ u ∈ A1, (B1.filter (G.Adj u)).card = 3 := by
    intro u hu
    rw [Finset.mem_filter] at hu
    have hsub : ∀ w, G.Adj u w → w ∈ B1 := by
      intro w hw
      have hc : c u ≠ c w := (c.map_rel hw).ne
      have hcases := hadj hu.1 hw
      rw [Finset.mem_filter]
      obtain hw_c1 | rfl := hcases
      · refine ⟨hw_c1, ?_⟩
        intro hcw
        rw [hu.2, hcw] at hc
        exact hc rfl
      · exfalso
        exact hc hu.2
    have h_eq : B1.filter (G.Adj u) = G.neighborFinset u := by
      ext w
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨-, hw⟩; exact hw
      · intro hw; exact ⟨hsub w hw, hw⟩
    have hd : (B1.filter (G.Adj u)).card = G.degree u := congr_arg Finset.card h_eq
    rw [hd, hreg u]
  have h_B1_deg : ∀ w ∈ B1, (A1.filter (G.Adj w)).card + (if G.Adj w v then 1 else 0) = 3 := by
    intro w hw
    rw [Finset.mem_filter] at hw
    have hvA1 : v ∉ A1 := fun h => hv (Finset.mem_filter.mp h).1
    have hsub : ∀ z, G.Adj w z → z ∈ A1 ∨ z = v := by
      intro z hz
      have hc : c z ≠ c w := (c.map_rel hz).symm.ne
      have hcases := hadj hw.1 hz
      obtain hz_c1 | rfl := hcases
      · left
        rw [Finset.mem_filter]
        refine ⟨hz_c1, ?_⟩
        exact connected_cubic_bipartite_has_no_cut_vertex_fin2_eq_of_ne_of_ne hc hw.2.symm
      · right
        rfl
    by_cases hadjv : G.Adj w v
    · simp only [hadjv, ite_true]
      have h_eq : G.neighborFinset w = insert v (A1.filter (G.Adj w)) := by
        ext z
        simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_filter]
        constructor
        · intro hz
          obtain hz' | rfl := hsub z hz
          · exact Or.inr ⟨hz', hz⟩
          · exact Or.inl rfl
        · rintro (rfl | ⟨-, hz⟩)
          · exact hadjv
          · exact hz
      have hv_not_mem : v ∉ A1.filter (G.Adj w) := by
        simp [hvA1]
      have hd : G.degree w = (insert v (A1.filter (G.Adj w))).card := congr_arg Finset.card h_eq
      rw [Finset.card_insert_of_notMem hv_not_mem] at hd
      have := hreg w
      omega
    · simp only [hadjv, ite_false, add_zero]
      have h_eq : G.neighborFinset w = A1.filter (G.Adj w) := by
        ext z
        simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter]
        constructor
        · intro hz
          obtain hz' | rfl := hsub z hz
          · exact ⟨hz', hz⟩
          · exact (hadjv hz).elim
        · rintro ⟨-, hz⟩
          exact hz
      have hd : G.degree w = (A1.filter (G.Adj w)).card := congr_arg Finset.card h_eq
      rw [← hd, hreg w]
  have h_sum_A1 : ∑ u ∈ A1, (B1.filter (G.Adj u)).card = 3 * A1.card := by
    have : ∑ u ∈ A1, (B1.filter (G.Adj u)).card = ∑ u ∈ A1, 3 := Finset.sum_congr rfl h_A1_deg
    rw [this]
    simp [mul_comm]
  have h_sum_B1 : (∑ w ∈ B1, (A1.filter (G.Adj w)).card) + (B1.filter (fun w => G.Adj w v)).card = 3 * B1.card := by
    have h_card : (B1.filter (fun w => G.Adj w v)).card = ∑ w ∈ B1, (if G.Adj w v then 1 else 0) := by
      rw [Finset.card_filter]
    rw [h_card, ← Finset.sum_add_distrib]
    have : ∑ w ∈ B1, ((A1.filter (G.Adj w)).card + (if G.Adj w v then 1 else 0)) = ∑ w ∈ B1, 3 :=
      Finset.sum_congr rfl h_B1_deg
    rw [this]
    simp [mul_comm]
  have h_filter_eq : B1.filter (fun w => G.Adj w v) = C1.filter (fun w => G.Adj w v) := by
    rw [hB1_eq]
    ext w
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hw, -⟩, hadj'⟩
      exact ⟨hw, hadj'⟩
    · rintro ⟨hw, hadj'⟩
      have hc : c w ≠ c v := (c.map_rel hadj').ne
      exact ⟨⟨hw, hc⟩, hadj'⟩
  let k := (C1.filter (fun w => G.Adj w v)).card
  have hdvd : 3 ∣ k := by
    have h_edges := connected_cubic_bipartite_has_no_cut_vertex_sum_bipartite_edges G A1 B1
    have hk_eq : k = (B1.filter (fun w => G.Adj w v)).card := h_filter_eq.symm ▸ rfl
    have h_eq : 3 * A1.card + k = 3 * B1.card := by
      rw [hk_eq, ← h_sum_A1, h_edges, h_sum_B1]
    have : k = 3 * (B1.card - A1.card) := by omega
    rw [this]
    exact dvd_mul_right 3 (B1.card - A1.card)
  have hk_sub : C1.filter (fun w => G.Adj w v) ⊆ G.neighborFinset v := by
    intro w hw
    rw [Finset.mem_filter] at hw
    rw [SimpleGraph.mem_neighborFinset]
    exact hw.2.symm
  have hdeg : G.degree v = 3 := hreg v
  have hk_le : k ≤ 3 := by
    have := Finset.card_le_card hk_sub
    rw [← hdeg]
    exact this
  have hk_ne_zero : k ≠ 0 := by
    intro hk0
    have hv' : (v : V) ∉ (C1 : Set V) := fun h => hv (Finset.mem_coe.mp h)
    obtain ⟨a, ha, b, hb, hab⟩ := connected_cubic_bipartite_has_no_cut_vertex_exists_adj_of_connected G hconn (C1 : Set V) (Finset.mem_coe.mpr hx) hv'
    rw [Finset.mem_coe] at ha hb
    have hcases := hadj ha hab
    obtain hb_c1 | hb_v := hcases
    · exact hb hb_c1
    · rw [hb_v] at hab
      have ha_mem : a ∈ C1.filter (fun w => G.Adj w v) := by
        rw [Finset.mem_filter]
        exact ⟨ha, hab⟩
      have : 0 < (C1.filter (fun w => G.Adj w v)).card := Finset.card_pos.mpr ⟨a, ha_mem⟩
      omega
  have hk_ne_three : k ≠ 3 := by
    intro hk3
    have h_eq : C1.filter (fun w => G.Adj w v) = G.neighborFinset v := by
      apply Finset.eq_of_subset_of_card_le hk_sub
      change (G.neighborFinset v).card ≤ k
      rw [hk3, ← hdeg]
      exact le_rfl
    have h_neigh_sub : ∀ w, G.Adj v w → w ∈ C1 := by
      intro w hw
      have : w ∈ G.neighborFinset v := by
        rw [SimpleGraph.mem_neighborFinset]
        exact hw
      rw [← h_eq, Finset.mem_filter] at this
      exact this.1
    let S : Set V := insert v (C1 : Set V)
    have hy_not_S : y.1 ∉ S := by
      intro hyS
      cases hyS with
      | inl h => exact y.2 h
      | inr h => exact hy (Finset.mem_coe.mp h)
    obtain ⟨a, ha, b, hb, hab⟩ := connected_cubic_bipartite_has_no_cut_vertex_exists_adj_of_connected G hconn S (Set.mem_insert v (C1 : Set V)) hy_not_S
    cases ha with
    | inl ha_v =>
      subst ha_v
      exact hb (Or.inr (Finset.mem_coe.mpr (h_neigh_sub b hab)))
    | inr ha_c1 =>
      rw [Finset.mem_coe] at ha_c1
      have hcases := hadj ha_c1 hab
      obtain hb_c1 | hb_v := hcases
      · exact hb (Or.inr (Finset.mem_coe.mpr hb_c1))
      · apply hb
        rw [hb_v]
        exact Or.inl rfl
  obtain ⟨m, hm⟩ := hdvd
  omega
