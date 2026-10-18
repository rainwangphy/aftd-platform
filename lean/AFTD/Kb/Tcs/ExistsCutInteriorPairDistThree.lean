import AFTD.Prelude

/-!
# exists_cut_interior_pair_dist_three

Topic: graphs   Node: adbd84116438

Provenance: helper lemma. step towards exists_dist_three_cut_potential_witness

If a cut (X, Xᶜ) has fewer edges than δ(G), then there exists a vertex x ∈ Xᶜ with no neighbours in X and a vertex y ∈ X with no neighbours in Xᶜ such that dist(x, y) = 3.
-/

lemma exists_cut_interior_pair_dist_three_aux_walk
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (X : Finset V) {u v : V}
    (p : G.Walk u v) (hu : u ∈ X) (hv : v ∈ (Xᶜ : Finset V)) :
    ∃ a ∈ X, ∃ b ∈ (Xᶜ : Finset V), G.Adj a b := by
  by_contra h
  push_neg at h
  have hstay : ∀ i ≤ p.length, p.getVert i ∈ X := by
    intro i
    induction i with
    | zero =>
      intro _
      simpa using hu
    | succ n ih =>
      intro hn
      have hnX : p.getVert n ∈ X := ih (Nat.le_of_succ_le hn)
      by_contra hc
      have hcY : p.getVert (n + 1) ∈ (Xᶜ : Finset V) := by
        rw [Finset.mem_compl]
        exact hc
      exact h (p.getVert n) hnX (p.getVert (n + 1)) hcY (p.adj_getVert_succ hn)
  have hp : p.getVert p.length ∈ X := hstay p.length le_rfl
  have hvY : p.getVert p.length ∈ (Xᶜ : Finset V) := by
    simpa [SimpleGraph.Walk.getVert_length] using hv
  rw [Finset.mem_compl] at hvY
  exact hvY hp

lemma exists_cut_interior_pair_dist_three_aux_cut
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (X : Finset V)
    (hX1 : X.Nonempty) (hX2 : (Xᶜ : Finset V).Nonempty) :
    ∃ a ∈ X, ∃ b ∈ (Xᶜ : Finset V), G.Adj a b := by
  obtain ⟨a, ha⟩ := hX1
  obtain ⟨b, hb⟩ := hX2
  obtain ⟨p⟩ := hG.preconnected a b
  exact exists_cut_interior_pair_dist_three_aux_walk G X p ha hb

lemma exists_cut_interior_pair_dist_three_aux_interior
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V)
    (hk : (G.edgeFinset.filter (fun e => ∃ a ∈ S, ∃ b ∈ (Sᶜ : Finset V), e = s(a, b))).card
      < G.minDegree)
    (u : V) (hu : u ∈ S) :
    ∃ y ∈ S, G.Adj u y ∧ ∀ z ∈ (Sᶜ : Finset V), ¬ G.Adj y z := by
  classical
  by_contra hcon
  push_neg at hcon
  let C := G.edgeFinset.filter (fun e => ∃ a ∈ S, ∃ b ∈ (Sᶜ : Finset V), e = s(a, b))
  change C.card < G.minDegree at hk
  let f : ↥(G.neighborFinset u) → ↥C := fun y =>
    if hy : (y : V) ∈ S then
      ⟨s((y : V), Classical.choose (hcon (y : V) hy ((G.mem_neighborFinset u (y : V)).mp y.2))), by
        obtain ⟨hzY, hzy⟩ := Classical.choose_spec (hcon (y : V) hy ((G.mem_neighborFinset u (y : V)).mp y.2))
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · exact (G.mem_edgeFinset).mpr ((G.mem_edgeSet).mpr hzy)
        · exact ⟨(y : V), hy, _, hzY, rfl⟩⟩
    else
      ⟨s(u, (y : V)), by
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · exact (G.mem_edgeFinset).mpr ((G.mem_edgeSet).mpr ((G.mem_neighborFinset u (y : V)).mp y.2))
        · refine ⟨u, hu, (y : V), ?_, rfl⟩
          rw [Finset.mem_compl]
          exact hy⟩
  have hinj : Function.Injective f := by
    intro y1 y2 h
    have hval : (f y1).1 = (f y2).1 := congrArg Subtype.val h
    simp only [f] at hval
    split_ifs at hval with hy1 hy2 hy2 hy1
    · have adj1 : G.Adj u ↑y1 := (G.mem_neighborFinset u ↑y1).mp y1.2
      have adj2 : G.Adj u ↑y2 := (G.mem_neighborFinset u ↑y2).mp y2.2
      rw [Sym2.eq_iff] at hval
      obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := hval
      · exact Subtype.ext h1
      · exfalso
        have hz2Y : Classical.choose (hcon ↑y2 hy2 adj2) ∈ (Sᶜ : Finset V) :=
          (Classical.choose_spec (hcon ↑y2 hy2 adj2)).1
        have hY : ↑y1 ∈ (Sᶜ : Finset V) := h1.symm ▸ hz2Y
        rw [Finset.mem_compl] at hY
        exact hY hy1
    · exfalso
      have adj1 : G.Adj u ↑y1 := (G.mem_neighborFinset u ↑y1).mp y1.2
      have adj2 : G.Adj u ↑y2 := (G.mem_neighborFinset u ↑y2).mp y2.2
      have hz1Y : Classical.choose (hcon ↑y1 hy1 adj1) ∈ (Sᶜ : Finset V) :=
        (Classical.choose_spec (hcon ↑y1 hy1 adj1)).1
      rw [Sym2.eq_iff] at hval
      obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := hval
      · exact adj1.ne' h1
      · exact hy2 (h1 ▸ hy1)
    · exfalso
      have adj1 : G.Adj u ↑y1 := (G.mem_neighborFinset u ↑y1).mp y1.2
      have adj2 : G.Adj u ↑y2 := (G.mem_neighborFinset u ↑y2).mp y2.2
      have hz2Y : Classical.choose (hcon ↑y2 hy2 adj2) ∈ (Sᶜ : Finset V) :=
        (Classical.choose_spec (hcon ↑y2 hy2 adj2)).1
      rw [Sym2.eq_iff] at hval
      obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := hval
      · exact adj2.ne h1
      · rw [Finset.mem_compl] at hz2Y
        exact hz2Y (h1 ▸ hu)
    · have adj1 : G.Adj u ↑y1 := (G.mem_neighborFinset u ↑y1).mp y1.2
      have adj2 : G.Adj u ↑y2 := (G.mem_neighborFinset u ↑y2).mp y2.2
      rw [Sym2.eq_iff] at hval
      obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := hval
      · exact Subtype.ext h2
      · exfalso
        exact hy1 (h2.symm ▸ hu)
  have hcard := Finset.card_le_card_of_injective (s := G.neighborFinset u) (t := C) hinj
  rw [G.card_neighborFinset_eq_degree] at hcard
  have hmin := G.minDegree_le_degree u
  omega

lemma exists_cut_interior_pair_dist_three_aux_cut_compl
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) :
    (G.edgeFinset.filter (fun e => ∃ a ∈ (Xᶜ : Finset V),
        ∃ b ∈ ((Xᶜ : Finset V)ᶜ : Finset V), e = s(a, b)))
    = (G.edgeFinset.filter (fun e => ∃ a ∈ X, ∃ b ∈ (Xᶜ : Finset V), e = s(a, b))) := by
  classical
  apply Finset.filter_congr
  intro e _
  simp only [Finset.mem_compl]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [not_not] at hb
    exact ⟨b, hb, a, ha, Sym2.eq_swap⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨b, hb, a, by rw [not_not]; exact ha, Sym2.eq_swap⟩

/-- In a connected graph with |E(X, Xᶜ)| < δ(G) and diam(G) ≥ 3, there exists an interior pair at distance 3. -/
theorem exists_cut_interior_pair_dist_three
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hd : 3 ≤ G.diam) (X : Finset V)
    (hX1 : X.Nonempty) (hX2 : (Xᶜ : Finset V).Nonempty)
    (hk : (G.edgeFinset.filter (fun e => ∃ u ∈ X, ∃ v ∈ (Xᶜ : Finset V), e = s(u, v))).card
      < G.minDegree) :
    ∃ (x y : V), G.dist x y = 3 ∧
      x ∈ (Xᶜ : Finset V) ∧ (∀ u ∈ X, ¬ G.Adj x u) ∧
      y ∈ X ∧ (∀ w ∈ (Xᶜ : Finset V), ¬ G.Adj y w) := by
  classical
  let Y : Finset V := (Xᶜ : Finset V)
  have hkY : (G.edgeFinset.filter (fun e => ∃ a ∈ Y, ∃ b ∈ (Yᶜ : Finset V), e = s(a, b))).card
      < G.minDegree := by
    dsimp [Y]
    rw [exists_cut_interior_pair_dist_three_aux_cut_compl]
    exact hk
  obtain ⟨a, haX, b, hbY, hab⟩ :=
    exists_cut_interior_pair_dist_three_aux_cut G hG X hX1 hX2
  obtain ⟨y, hyX, hay, hy_int⟩ :=
    exists_cut_interior_pair_dist_three_aux_interior G X hk a haX
  obtain ⟨x, hxY, hbx, hx_int⟩ :=
    exists_cut_interior_pair_dist_three_aux_interior G Y hkY b hbY
  have hx_intX : ∀ u ∈ X, ¬ G.Adj x u := by
    intro u hu
    exact hx_int u (by dsimp [Y] at hu ⊢; simpa using hu)
  have hx_mem : x ∈ (Xᶜ : Finset V) := by simpa [Y] using hxY
  have hy_mem : y ∈ X := hyX
  have hy_intY : ∀ w ∈ (Xᶜ : Finset V), ¬ G.Adj y w := hy_int
  let p : G.Walk y x := SimpleGraph.Walk.cons hay.symm
    (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbx (SimpleGraph.Walk.nil)))
  have hp : p.length = 3 := by simp [p]
  have hle : G.dist x y ≤ 3 := by
    have hpy : G.dist y x ≤ p.length := G.dist_le p
    rw [hp] at hpy
    rwa [SimpleGraph.dist_comm] at hpy
  have hxy_ne : x ≠ y := by
    intro hxy
    have hxX : x ∈ X := by rw [hxy]; exact hy_mem
    rw [Finset.mem_compl] at hx_mem
    exact hx_mem hxX
  have hxy_not_adj : ¬ G.Adj x y := hx_intX y hy_mem
  have hcommon : G.commonNeighbors x y = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    intro hne
    obtain ⟨z, hz⟩ := hne
    rw [G.mem_commonNeighbors] at hz
    obtain ⟨hxz, hyz⟩ := hz
    by_cases hzX : z ∈ X
    · exact hx_intX z hzX hxz
    · have hzY : z ∈ (Xᶜ : Finset V) := by rw [Finset.mem_compl]; exact hzX
      exact hy_intY z hzY hyz
  have hed : 2 < G.edist x y := by
    rw [SimpleGraph.two_lt_edist_iff]
    exact ⟨hxy_ne, hxy_not_adj, hcommon⟩
  have hcast : (G.dist x y : ℕ∞) = G.edist x y := (hG x y).coe_dist_eq_edist
  have h2dist : 2 < G.dist x y := by
    have h2 : (2 : ℕ∞) < (G.dist x y : ℕ∞) := by
      rw [hcast]
      exact hed
    exact_mod_cast h2
  have hdist : G.dist x y = 3 := by omega
  exact ⟨x, y, hdist, hx_mem, hx_intX, hy_mem, hy_intY⟩
