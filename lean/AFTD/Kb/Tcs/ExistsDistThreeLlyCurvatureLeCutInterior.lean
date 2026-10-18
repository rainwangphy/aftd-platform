import AFTD.Prelude
import AFTD.Kb.Tcs.GraphLlyCurvatureLeOfLipschitzCutPotential
import AFTD.Kb.Tcs.GraphLlyCurvature
import AFTD.Kb.Tcs.GraphLlyCurvatureComm

/-!
# exists_dist_three_lly_curvature_le_cut_interior

Topic: graphs   Node: f1a984a62b6f

Provenance: helper lemma. step towards exists_dist_three_lly_curvature_le_cut

If x lies in the interior of X (all its neighbours in X) and y in the interior of Xᶜ, and d(x,y) = 3, then κ_LLY(x,y) ≤ 2·|E(X,Xᶜ)| / (3 δ(G)).
-/

/-- Interior-pair case of the cut bound on κ_LLY at distance 3. -/
theorem exists_dist_three_lly_curvature_le_cut_interior
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (X : Finset V) (x y : V)
    (hxX : x ∈ X) (hxint : ∀ w : V, G.Adj x w → w ∈ X)
    (hyX : y ∈ (Xᶜ : Finset V)) (hyint : ∀ w : V, G.Adj y w → w ∈ (Xᶜ : Finset V))
    (hd3 : G.dist x y = 3) :
    graph_lly_curvature G x y ≤
      (2 * ((G.edgeFinset.filter (fun e => ∃ u ∈ X, ∃ v ∈ (Xᶜ : Finset V), e = s(u, v))).card : ℝ)) /
        (3 * (G.minDegree : ℝ)) := by
  classical
  set X2 : Finset V := X.filter (fun z => ∀ w : V, G.Adj z w → w ∈ X) with hX2def
  have hX2sub : ∀ z ∈ X2, z ∈ X ∧ ∀ w : V, G.Adj z w → w ∈ X := by
    intro z hz; rw [hX2def, Finset.mem_filter] at hz; exact hz
  have hxX2 : x ∈ X2 := by
    rw [hX2def, Finset.mem_filter]; exact ⟨hxX, hxint⟩
  have hX2ne : X2.Nonempty := ⟨x, hxX2⟩
  let f : V → ℝ := fun v => ((X2.inf' hX2ne (fun z => G.dist v z) : ℕ) : ℝ)
  have hfval : ∀ v : V, f v = ((X2.inf' hX2ne (fun z => G.dist v z) : ℕ) : ℝ) := fun v => rfl
  set C : Finset (Sym2 V) :=
    G.edgeFinset.filter (fun e => ∃ u ∈ X, ∃ v ∈ (Xᶜ : Finset V), e = s(u, v)) with hC
  set S2 : Finset V := (G.neighborFinset y).filter (fun b => f b = 2) with hS2
  set S1 : Finset V := (G.neighborFinset x).filter (fun a => a ∉ X2) with hS1
  have hxy : x ≠ y := by intro h; rw [h, SimpleGraph.dist_self] at hd3; omega
  have hfx : f x = 0 := by
    have h1 : X2.inf' hX2ne (fun z => G.dist x z) ≤ G.dist x x := Finset.inf'_le _ hxX2
    rw [SimpleGraph.dist_self] at h1
    have h2 : (0:ℕ) ≤ X2.inf' hX2ne (fun z => G.dist x z) := Nat.zero_le _
    have hinf : X2.inf' hX2ne (fun z => G.dist x z) = 0 := le_antisymm h1 h2
    rw [hfval, hinf]; norm_num
  have hge : ∀ z ∈ X2, 3 ≤ G.dist y z := by
    intro z hz
    obtain ⟨hzX, hzint⟩ := hX2sub z hz
    by_contra hlt
    push Not at hlt
    have hzy : z ≠ y := by
      intro h; rw [h] at hzX; rw [Finset.mem_compl] at hyX; exact hyX hzX
    have hyz_ne : G.dist y z ≠ 0 := by
      rw [SimpleGraph.dist_ne_zero_iff_ne_and_reachable]
      exact ⟨fun h => hzy h.symm, hG y z⟩
    have : G.dist y z = 1 ∨ G.dist y z = 2 := by omega
    rcases this with h1 | h2
    · have hadj : G.Adj y z := by rw [← SimpleGraph.dist_eq_one_iff_adj, h1]
      have hzc : z ∈ (Xᶜ : Finset V) := hyint z hadj
      rw [Finset.mem_compl] at hzc; exact hzc hzX
    · obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist y z
      have hp2 : p.length = 2 := by rw [hp, h2]
      have hadjyc : G.Adj y (p.getVert 1) := by
        have := p.adj_getVert_succ (i := 0) (by rw [hp2]; omega); simpa using this
      have hadjcz : G.Adj z (p.getVert 1) := by
        have h := p.adj_getVert_succ (i := 1) (by rw [hp2]; omega)
        have h2' : p.getVert 2 = z := by rw [← hp2]; exact p.getVert_length
        rw [h2'] at h; exact h.symm
      have hcXc : p.getVert 1 ∈ (Xᶜ : Finset V) := hyint _ hadjyc
      rw [Finset.mem_compl] at hcXc
      exact hcXc (hzint _ hadjcz)
  have hfy : f y = 3 := by
    have hle : X2.inf' hX2ne (fun z => G.dist y z) ≤ 3 := by
      have := Finset.inf'_le (fun z => G.dist y z) hxX2
      rwa [SimpleGraph.dist_comm, hd3] at this
    have hge' : 3 ≤ X2.inf' hX2ne (fun z => G.dist y z) := Finset.le_inf' hX2ne _ hge
    have hinf : X2.inf' hX2ne (fun z => G.dist y z) = 3 := le_antisymm hle hge'
    rw [hfval, hinf]; norm_num
  have hf : ∀ a b : V, f a - f b ≤ (G.dist a b : ℝ) := by
    intro a b
    obtain ⟨z0, hz0mem, hz0eq⟩ := Finset.exists_mem_eq_inf' hX2ne (fun z => G.dist b z)
    have h1 : X2.inf' hX2ne (fun z => G.dist a z) ≤ G.dist a z0 := Finset.inf'_le _ hz0mem
    have h2 : G.dist a z0 ≤ G.dist a b + G.dist b z0 :=
      SimpleGraph.Reachable.dist_triangle_left (hG a b) z0
    have hds : X2.inf' hX2ne (fun z => G.dist a z) ≤
        X2.inf' hX2ne (fun z => G.dist b z) + G.dist a b := by
      rw [hz0eq]; omega
    have hcast : ((X2.inf' hX2ne (fun z => G.dist a z) : ℕ) : ℝ) ≤
        ((X2.inf' hX2ne (fun z => G.dist b z) : ℕ) : ℝ) + (G.dist a b : ℝ) := by
      have hc := (Nat.cast_le (α := ℝ)).mpr hds; rw [Nat.cast_add] at hc; exact hc
    rw [hfval, hfval]
    linarith
  have h2le : ∀ b ∈ G.neighborFinset y, (2:ℝ) ≤ f b := by
    intro b hb
    have hyb : G.Adj y b := (SimpleGraph.mem_neighborFinset G y b).mp hb
    have hbXc : b ∉ X := by
      have := hyint b hyb; rwa [Finset.mem_compl] at this
    have hge2 : ∀ z ∈ X2, 2 ≤ G.dist b z := by
      intro z hz
      obtain ⟨hzX, hzint⟩ := hX2sub z hz
      have hbz : b ≠ z := by intro h; exact hbXc (h ▸ hzX)
      have hne0 : G.dist b z ≠ 0 := by
        rw [SimpleGraph.dist_ne_zero_iff_ne_and_reachable]
        exact ⟨hbz, hG b z⟩
      have hne1 : G.dist b z ≠ 1 := by
        intro h
        have hzb : G.dist z b = 1 := by rw [SimpleGraph.dist_comm]; exact h
        exact hbXc (hzint b (SimpleGraph.dist_eq_one_iff_adj.mp hzb))
      omega
    have := Finset.le_inf' hX2ne (fun z => G.dist b z) hge2
    rw [hfval]
    exact_mod_cast this
  have hS2k : S2.card ≤ C.card := by
    have hex : ∀ b ∈ S2, ∃ c : V, G.Adj b c ∧ c ∈ X := by
      intro b hb
      rw [hS2, Finset.mem_filter] at hb
      obtain ⟨hbN, hfb⟩ := hb
      obtain ⟨z, hzmem, hzeq⟩ := Finset.exists_mem_eq_inf' hX2ne (fun z => G.dist b z)
      have hcast : ((X2.inf' hX2ne (fun z => G.dist b z) : ℕ) : ℝ) = 2 := by
        rw [← hfval b]; exact hfb
      have hdseq : X2.inf' hX2ne (fun z => G.dist b z) = 2 := by exact_mod_cast hcast
      have hzdist : G.dist b z = 2 := by rw [← hzeq, hdseq]
      obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist b z
      have hp2 : p.length = 2 := by rw [hp, hzdist]
      refine ⟨p.getVert 1, ?_, ?_⟩
      · have := p.adj_getVert_succ (i := 0) (by rw [hp2]; omega); simpa using this
      · have hzX := (hX2sub z hzmem).2
        have hadj : G.Adj (p.getVert 1) z := by
          have h := p.adj_getVert_succ (i := 1) (by rw [hp2]; omega)
          have h2' : p.getVert 2 = z := by rw [← hp2]; exact p.getVert_length
          rwa [h2'] at h
        exact hzX _ hadj.symm
    let φ : V → Sym2 V := fun b => if h : ∃ c : V, G.Adj b c ∧ c ∈ X then s(h.choose, b) else s(b, b)
    apply Finset.card_le_card_of_injOn φ
    · intro b hb
      have hb' : b ∈ S2 := hb
      rw [hS2, Finset.mem_filter] at hb'
      obtain ⟨hbN, hfb⟩ := hb'
      have hbXc : b ∈ (Xᶜ : Finset V) := hyint b ((SimpleGraph.mem_neighborFinset G y b).mp hbN)
      rw [Finset.mem_compl] at hbXc
      have hh := hex b hb
      have hφb : φ b = s(hh.choose, b) := by simp only [φ]; exact dif_pos hh
      have hspec := hh.choose_spec
      rw [Finset.mem_coe, hC, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [hφb, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact hspec.1.symm
      · rw [hφb]
        exact ⟨hh.choose, hspec.2, b, by rw [Finset.mem_compl]; exact hbXc, rfl⟩
    · intro b1 hb1 b2 hb2 heq
      have hb1' : b1 ∈ S2 := hb1
      have hb2' : b2 ∈ S2 := hb2
      rw [hS2, Finset.mem_filter] at hb1' hb2'
      obtain ⟨hb1N, _⟩ := hb1'
      obtain ⟨hb2N, _⟩ := hb2'
      have hb1Xc : b1 ∈ (Xᶜ : Finset V) := hyint b1 ((SimpleGraph.mem_neighborFinset G y b1).mp hb1N)
      have hb2Xc : b2 ∈ (Xᶜ : Finset V) := hyint b2 ((SimpleGraph.mem_neighborFinset G y b2).mp hb2N)
      rw [Finset.mem_compl] at hb1Xc hb2Xc
      have hh1 := hex b1 hb1
      have hh2 := hex b2 hb2
      have hφ1 : φ b1 = s(hh1.choose, b1) := by simp only [φ]; exact dif_pos hh1
      have hφ2 : φ b2 = s(hh2.choose, b2) := by simp only [φ]; exact dif_pos hh2
      rw [hφ1, hφ2] at heq
      by_contra hne
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hne h2
      · exact hb1Xc (h2 ▸ hh2.choose_spec.2)
  have hS1k : S1.card ≤ C.card := by
    have hex : ∀ b ∈ S1, ∃ w : V, G.Adj b w ∧ w ∉ X := by
      intro b hb
      rw [hS1, Finset.mem_filter] at hb
      obtain ⟨hbN, hbX2⟩ := hb
      have hbX : b ∈ X := hxint b ((SimpleGraph.mem_neighborFinset G x b).mp hbN)
      by_contra h
      push Not at h
      exact hbX2 (by rw [hX2def, Finset.mem_filter]; exact ⟨hbX, h⟩)
    let φ : V → Sym2 V := fun b => if h : ∃ w : V, G.Adj b w ∧ w ∉ X then s(b, h.choose) else s(b, b)
    apply Finset.card_le_card_of_injOn φ
    · intro b hb
      have hb' : b ∈ S1 := hb
      rw [hS1, Finset.mem_filter] at hb'
      obtain ⟨hbN, hbX2⟩ := hb'
      have hbX : b ∈ X := hxint b ((SimpleGraph.mem_neighborFinset G x b).mp hbN)
      have hh := hex b hb
      have hφb : φ b = s(b, hh.choose) := by simp only [φ]; exact dif_pos hh
      have hspec := hh.choose_spec
      rw [Finset.mem_coe, hC, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [hφb, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact hspec.1
      · rw [hφb]
        exact ⟨b, hbX, hh.choose, by rw [Finset.mem_compl]; exact hspec.2, rfl⟩
    · intro b1 hb1 b2 hb2 heq
      have hb1' : b1 ∈ S1 := hb1
      rw [hS1, Finset.mem_filter] at hb1'
      obtain ⟨hb1N, _⟩ := hb1'
      have hb1X : b1 ∈ X := hxint b1 ((SimpleGraph.mem_neighborFinset G x b1).mp hb1N)
      have hh1 := hex b1 hb1
      have hh2 := hex b2 hb2
      have hφ1 : φ b1 = s(b1, hh1.choose) := by simp only [φ]; exact dif_pos hh1
      have hφ2 : φ b2 = s(b2, hh2.choose) := by simp only [φ]; exact dif_pos hh2
      rw [hφ1, hφ2] at heq
      by_contra hne
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hne h1
      · exact hh2.choose_spec.2 (h1 ▸ hb1X)
  have hAxfull : (∑ a ∈ G.neighborFinset x, f a) = (S1.card : ℝ) := by
    have hterm : ∀ a ∈ G.neighborFinset x, f a = (if a ∉ X2 then (1:ℝ) else 0) := by
      intro a ha
      have hax : G.Adj x a := (SimpleGraph.mem_neighborFinset G x a).mp ha
      have hdx : G.dist a x = 1 := by
        rw [SimpleGraph.dist_comm]; exact SimpleGraph.dist_eq_one_iff_adj.mpr hax
      have hfle : f a ≤ 1 := by
        rw [hfval]
        have h1 : X2.inf' hX2ne (fun z => G.dist a z) ≤ G.dist a x := Finset.inf'_le _ hxX2
        rw [hdx] at h1
        have h2 : ((X2.inf' hX2ne (fun z => G.dist a z) : ℕ) : ℝ) ≤ 1 := by exact_mod_cast h1
        linarith
      by_cases h : a ∈ X2
      · have hz : f a = 0 := by
          rw [hfval]
          have h1 : X2.inf' hX2ne (fun z => G.dist a z) ≤ G.dist a a := Finset.inf'_le _ h
          rw [SimpleGraph.dist_self] at h1
          have h2 : (0:ℕ) ≤ X2.inf' hX2ne (fun z => G.dist a z) := Nat.zero_le _
          have hinf : X2.inf' hX2ne (fun z => G.dist a z) = 0 := le_antisymm h1 h2
          rw [hinf]; norm_num
        rw [hz, if_neg (by simp [h])]
      · have hge1 : 1 ≤ f a := by
          rw [hfval]
          have hge' : ∀ z ∈ X2, 1 ≤ G.dist a z := by
            intro z hz
            have haz : a ≠ z := by intro hh; exact h (hh ▸ hz)
            have hne : G.dist a z ≠ 0 := by
              rw [SimpleGraph.dist_ne_zero_iff_ne_and_reachable]
              exact ⟨haz, hG a z⟩
            omega
          have := Finset.le_inf' hX2ne (fun z => G.dist a z) hge'
          exact_mod_cast this
        rw [if_pos h]; linarith
    rw [Finset.sum_congr rfl hterm, Finset.sum_boole, hS1]
  have hAyfull : (∑ b ∈ G.neighborFinset y, (3 - f b)) ≤ (S2.card : ℝ) := by
    have hterm : ∀ b ∈ G.neighborFinset y, (3 - f b) ≤ (if f b = 2 then (1:ℝ) else 0) := by
      intro b hb
      have h2 := h2le b hb
      obtain ⟨m, hm⟩ : ∃ m : ℕ, f b = (m:ℝ) := ⟨_, hfval b⟩
      rw [hm] at h2 ⊢
      split_ifs with h
      · linarith
      · have hne : (2:ℝ) ≠ (m:ℝ) := fun hh => h hh.symm
        have hgt : (2:ℝ) < (m:ℝ) := lt_of_le_of_ne h2 hne
        have hgtm : 2 < m := by exact_mod_cast hgt
        have h3m : (3:ℝ) ≤ (m:ℝ) := by exact_mod_cast (by omega : 3 ≤ m)
        linarith
    calc (∑ b ∈ G.neighborFinset y, (3 - f b))
        ≤ ∑ b ∈ G.neighborFinset y, (if f b = 2 then (1:ℝ) else 0) := Finset.sum_le_sum hterm
      _ = (S2.card : ℝ) := by rw [Finset.sum_boole, hS2]
  have hval : f y - f x = (G.dist y x : ℝ) := by rw [hfy, hfx, SimpleGraph.dist_comm, hd3]; norm_num
  have hpot := graph_lly_curvature_le_of_lipschitz_cut_potential G hG y x hxy.symm f hf hval
  have hdist : (G.dist y x : ℝ) = 3 := by rw [SimpleGraph.dist_comm, hd3]; norm_num
  rw [hdist] at hpot
  haveI : Nontrivial V := ⟨⟨x, y, hxy⟩⟩
  have hδ0 : 0 < G.minDegree := SimpleGraph.Preconnected.minDegree_pos_of_nontrivial hG.preconnected
  have hδR : (0:ℝ) < (G.minDegree : ℝ) := by exact_mod_cast hδ0
  have hdyδ : (G.minDegree : ℝ) ≤ (G.degree y : ℝ) := by exact_mod_cast G.minDegree_le_degree y
  have hdxδ : (G.minDegree : ℝ) ≤ (G.degree x : ℝ) := by exact_mod_cast G.minDegree_le_degree x
  have hdy : (0:ℝ) < (G.degree y : ℝ) := lt_of_lt_of_le hδR hdyδ
  have hdx : (0:ℝ) < (G.degree x : ℝ) := lt_of_lt_of_le hδR hdxδ
  have hAy : 3 - (∑ b ∈ G.neighborFinset y, f b) / (G.degree y : ℝ)
      ≤ (S2.card : ℝ) / (G.degree y : ℝ) := by
    have he : 3 - (∑ b ∈ G.neighborFinset y, f b) / (G.degree y : ℝ)
        = (∑ b ∈ G.neighborFinset y, (3 - f b)) / (G.degree y : ℝ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
        nsmul_eq_mul]
      field_simp
    rw [he, div_le_div_iff_of_pos_right hdy]
    exact hAyfull
  have hAx : (∑ b ∈ G.neighborFinset x, f b) / (G.degree x : ℝ)
      ≤ (S1.card : ℝ) / (G.degree x : ℝ) := by
    rw [hAxfull]
  have hk : (S2.card : ℝ) ≤ (C.card : ℝ) := by exact_mod_cast hS2k
  have hk1 : (S1.card : ℝ) ≤ (C.card : ℝ) := by exact_mod_cast hS1k
  have harr : (S2.card : ℝ) / (G.degree y : ℝ) + (S1.card : ℝ) / (G.degree x : ℝ)
      ≤ 2 * (C.card : ℝ) / (G.minDegree : ℝ) := by
    have h1 : (S2.card : ℝ) / (G.degree y : ℝ) ≤ (C.card : ℝ) / (G.minDegree : ℝ) := by
      calc (S2.card : ℝ) / (G.degree y : ℝ) ≤ (S2.card : ℝ) / (G.minDegree : ℝ) := by gcongr
        _ ≤ (C.card : ℝ) / (G.minDegree : ℝ) := by gcongr
    have h2 : (S1.card : ℝ) / (G.degree x : ℝ) ≤ (C.card : ℝ) / (G.minDegree : ℝ) := by
      calc (S1.card : ℝ) / (G.degree x : ℝ) ≤ (S1.card : ℝ) / (G.minDegree : ℝ) := by gcongr
        _ ≤ (C.card : ℝ) / (G.minDegree : ℝ) := by gcongr
    calc (S2.card : ℝ) / (G.degree y : ℝ) + (S1.card : ℝ) / (G.degree x : ℝ)
        ≤ (C.card : ℝ) / (G.minDegree : ℝ) + (C.card : ℝ) / (G.minDegree : ℝ) := by linarith
      _ = 2 * (C.card : ℝ) / (G.minDegree : ℝ) := by ring
  rw [graph_lly_curvature_comm]
  have e2 : 2 * (C.card : ℝ) / (3 * (G.minDegree : ℝ))
      = (2 * (C.card : ℝ) / (G.minDegree : ℝ)) / 3 := by field_simp
  rw [e2]
  refine le_trans hpot ?_
  rw [div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 3)]
  linarith
