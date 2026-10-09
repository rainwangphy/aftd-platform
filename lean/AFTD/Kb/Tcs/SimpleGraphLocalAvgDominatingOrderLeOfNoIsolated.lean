import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphLocalAvgDominatingOrder
import AFTD.Kb.Tcs.SimpleGraphDominatingSetsContaining

/-!
# simple_graph_local_avg_dominating_order_le_of_no_isolated

Topic: graphs   Node: f65d0790df7a

Provenance: formalization of a published result. Source: arXiv:2610.11446 (On the local average order of dominating sets), Theorem 3.8, second statement (the first, the sum bound (n+1)/2 + ½ Σ_{u ∉ N[v]} (deg u + 1)/(2^{deg u + 1} − 1), is not stated here).

If the finite graph G of order n has no isolated vertices, then for every vertex v the dominating sets containing v have average size at most (5n − 2 deg(v) + 1)/6 (hence at most (5n − 1)/6).
-/

theorem simple_graph_local_avg_dominating_order_le_of_no_isolated {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hiso : ∀ w, 0 < G.degree w)
    (v : V) :
    simple_graph_local_avg_dominating_order G v ≤
      (5 * (Fintype.card V : ℚ) - 2 * G.degree v + 1) / 6 := by
  classical
  set D := simple_graph_dominating_sets_containing G v with hD
  set n := Fintype.card V with hn
  have memD : ∀ S, S ∈ D ↔ v ∈ S ∧ ∀ w, w ∈ S ∨ ∃ u ∈ S, G.Adj u w := by
    intro S; rw [hD]; unfold simple_graph_dominating_sets_containing; simp
  -- `D` is closed under supersets
  have hup : ∀ S ∈ D, ∀ T, S ⊆ T → T ∈ D := by
    intro S hS T hST
    rw [memD] at hS ⊢
    refine ⟨hST hS.1, fun w => ?_⟩
    rcases hS.2 w with h | ⟨u, hu, h⟩
    · exact Or.inl (hST h)
    · exact Or.inr ⟨u, hST hu, h⟩
  have hDne : D.Nonempty :=
    ⟨Finset.univ, (memD _).2 ⟨Finset.mem_univ v, fun w => Or.inl (Finset.mem_univ w)⟩⟩
  -- closed neighbourhoods and the vertices outside `N[v]`
  set N : V → Finset V := fun w => insert w (G.neighborFinset w) with hN
  set U : Finset V := (Finset.univ.erase v) \ G.neighborFinset v with hU
  have hUcard : U.card = n - 1 - G.degree v := by
    rw [hU, Finset.card_sdiff_of_subset, Finset.card_erase_of_mem (Finset.mem_univ v),
      G.card_neighborFinset_eq_degree]
    · rfl
    · intro w hw
      rw [Finset.mem_erase]
      exact ⟨(G.ne_of_adj ((G.mem_neighborFinset v w).1 hw)).symm, Finset.mem_univ w⟩
  have hdegle : G.degree v ≤ n - 1 := by
    rw [← G.card_neighborFinset_eq_degree]
    have : G.neighborFinset v ⊆ Finset.univ.erase v := by
      intro w hw
      rw [Finset.mem_erase]
      exact ⟨(G.ne_of_adj ((G.mem_neighborFinset v w).1 hw)).symm, Finset.mem_univ w⟩
    calc (G.neighborFinset v).card ≤ (Finset.univ.erase v).card := Finset.card_le_card this
      _ = n - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ v)]; rfl
  have hn1 : 1 ≤ n := Fintype.card_pos_iff.2 ⟨v⟩
  -- counts: `a x` sets containing `x`, `b x` avoiding `x`, `c x` sets in which `x` is critical
  set a : V → ℕ := fun x => (D.filter (fun S => x ∈ S)).card with ha
  set b : V → ℕ := fun x => (D.filter (fun S => x ∉ S)).card with hb
  set c : V → ℕ := fun x => (D.filter (fun S => x ∈ S ∧ S.erase x ∉ D)).card with hc
  have hab : ∀ x, a x + b x = D.card := fun x => Finset.card_filter_add_card_filter_not _
  have habc : ∀ x, a x = b x + c x := by
    intro x
    simp only [ha, hb, hc]
    have hsplit : (D.filter (fun S => x ∈ S)).card =
        ((D.filter (fun S => x ∈ S)).filter (fun S => S.erase x ∈ D)).card +
        ((D.filter (fun S => x ∈ S)).filter (fun S => ¬ S.erase x ∈ D)).card :=
      (Finset.card_filter_add_card_filter_not _).symm
    rw [Finset.filter_filter, Finset.filter_filter] at hsplit
    rw [hsplit]
    congr 1
    -- erasing `x` matches the sets with `x` removable with the sets avoiding `x`
    apply le_antisymm
    · have inj : Set.InjOn (fun S : Finset V => S.erase x)
          ↑(D.filter (fun S => x ∈ S ∧ S.erase x ∈ D)) := by
        intro S hS T hT h
        simp only [Finset.mem_coe, Finset.mem_filter] at hS hT
        rw [← Finset.insert_erase hS.2.1, ← Finset.insert_erase hT.2.1]
        exact congrArg (insert x) h
      rw [← Finset.card_image_of_injOn inj]
      apply Finset.card_le_card
      intro T hT
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hT
      simp only [Finset.mem_filter] at hS ⊢
      exact ⟨hS.2.2, by simp⟩
    · have inj : Set.InjOn (fun S : Finset V => insert x S) ↑(D.filter (fun S => x ∉ S)) := by
        intro S hS T hT h
        simp only [Finset.mem_coe, Finset.mem_filter] at hS hT
        rw [← Finset.erase_insert hS.2, ← Finset.erase_insert hT.2]
        exact congrArg (fun W => Finset.erase W x) h
      rw [← Finset.card_image_of_injOn inj]
      apply Finset.card_le_card
      intro T hT
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hT
      simp only [Finset.mem_filter] at hS ⊢
      refine ⟨hup S hS.1 _ (Finset.subset_insert x S), Finset.mem_insert_self x S, ?_⟩
      rw [Finset.erase_insert hS.2]; exact hS.1
  have hsum : ∑ S ∈ D, S.card = ∑ x, a x := by
    have h : ∀ S ∈ D, S.card = ∑ x, if x ∈ S then 1 else 0 := by
      intro S _
      rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [Finset.sum_congr rfl h, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [ha]; rw [Finset.card_filter]
  -- `x ≠ v` critical in `S`: `S` meets some `N[w]`, `w ∉ N[v]`, exactly in `x`
  set E : V → V → Finset (Finset V) := fun w x => D.filter (fun S => S ∩ N w = {x}) with hE
  have hcrit : ∀ x, x ≠ v → c x ≤ ∑ w ∈ U, (E w x).card := by
    intro x hxv
    simp only [hc]
    refine le_trans (Finset.card_le_card ?_) Finset.card_biUnion_le
    intro S hS
    rw [Finset.mem_filter] at hS
    obtain ⟨hSD, hxS, hSx⟩ := hS
    have hvS : v ∈ S.erase x := Finset.mem_erase.2 ⟨hxv.symm, ((memD S).1 hSD).1⟩
    rw [memD] at hSx
    push_neg at hSx
    obtain ⟨w, hwS, hwadj⟩ := hSx hvS
    have hNw : S ∩ N w = {x} := by
      ext y
      simp only [Finset.mem_inter, hN, Finset.mem_insert, G.mem_neighborFinset,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hyS, hy⟩
        by_contra hyx
        have hy' : y ∈ S.erase x := Finset.mem_erase.2 ⟨hyx, hyS⟩
        rcases hy with rfl | hy
        · exact hwS hy'
        · exact hwadj y hy' hy.symm
      · intro hyx
        rw [hyx]
        refine ⟨hxS, ?_⟩
        rcases ((memD S).1 hSD).2 w with h | ⟨u, hu, h⟩
        · left
          by_contra hne
          exact hwS (Finset.mem_erase.2 ⟨fun h' => hne h'.symm, h⟩)
        · right
          by_cases hux : u = x
          · rw [← hux]; exact h.symm
          · exact absurd h (hwadj u (Finset.mem_erase.2 ⟨hux, hu⟩))
    have hwU : w ∈ U := by
      rw [hU, Finset.mem_sdiff, Finset.mem_erase, G.mem_neighborFinset]
      refine ⟨⟨fun h => hwS (h ▸ hvS), Finset.mem_univ w⟩, fun h => hwadj v hvS h⟩
    exact Finset.mem_biUnion.2 ⟨w, hwU, Finset.mem_filter.2 ⟨hSD, hNw⟩⟩
  -- at most two thirds of the sets meet `N[w]` in a single vertex
  have hthird : ∀ w, 3 * (D.filter (fun S => (S ∩ N w).card = 1)).card ≤ 2 * D.card := by
    intro w
    obtain ⟨w', hw'⟩ : ∃ w', G.Adj w w' := by
      have := hiso w
      rw [← G.card_neighborFinset_eq_degree, Finset.card_pos] at this
      obtain ⟨w', hw'⟩ := this
      exact ⟨w', (G.mem_neighborFinset w w').1 hw'⟩
    have hww' : w ≠ w' := G.ne_of_adj hw'
    have hwN : w ∈ N w := by simp [hN]
    have hw'N : w' ∈ N w := by simp [hN, G.mem_neighborFinset, hw']
    set single := D.filter (fun S => (S ∩ N w).card = 1) with hsingle
    set multi := D.filter (fun S => ¬ (S ∩ N w).card = 1) with hmulti
    have hsm : single.card + multi.card = D.card := Finset.card_filter_add_card_filter_not _
    let φ : Finset V → Finset V := fun S => if w ∈ S then insert w' S else insert w S
    have hmaps : ∀ S ∈ single, φ S ∈ multi := by
      intro S hS
      rw [hsingle, Finset.mem_filter, Finset.card_eq_one] at hS
      obtain ⟨hSD, z, hz⟩ := hS
      rw [hmulti, Finset.mem_filter]
      by_cases hwS : w ∈ S
      · simp only [φ, if_pos hwS]
        refine ⟨hup S hSD _ (Finset.subset_insert _ _), fun h1 => ?_⟩
        have hw_in : w ∈ insert w' S ∩ N w := Finset.mem_inter.2 ⟨Finset.mem_insert_of_mem hwS, hwN⟩
        have hw'_in : w' ∈ insert w' S ∩ N w := Finset.mem_inter.2 ⟨Finset.mem_insert_self _ _, hw'N⟩
        exact hww' (Finset.card_le_one.1 h1.le w hw_in w' hw'_in)
      · simp only [φ, if_neg hwS]
        refine ⟨hup S hSD _ (Finset.subset_insert _ _), fun h1 => ?_⟩
        have hz_in : z ∈ S ∩ N w := by rw [hz]; exact Finset.mem_singleton_self z
        have hzw : z ≠ w := fun h => hwS (h ▸ (Finset.mem_inter.1 hz_in).1)
        have hw_in : w ∈ insert w S ∩ N w := Finset.mem_inter.2 ⟨Finset.mem_insert_self _ _, hwN⟩
        have hz_in' : z ∈ insert w S ∩ N w :=
          Finset.mem_inter.2 ⟨Finset.mem_insert_of_mem (Finset.mem_inter.1 hz_in).1,
            (Finset.mem_inter.1 hz_in).2⟩
        exact hzw (Finset.card_le_one.1 h1.le z hz_in' w hw_in)
    have hfib : ∀ M, (single.filter (fun S => φ S = M)).card ≤ 2 := by
      intro M
      refine le_trans (Finset.card_le_card (t := {M.erase w', M.erase w}) ?_) Finset.card_le_two
      intro S hS
      rw [Finset.mem_filter, hsingle, Finset.mem_filter, Finset.card_eq_one] at hS
      obtain ⟨⟨_, z, hz⟩, hφ⟩ := hS
      rw [Finset.mem_insert, Finset.mem_singleton]
      by_cases hwS : w ∈ S
      · left
        simp only [φ, if_pos hwS] at hφ
        have hw'S : w' ∉ S := by
          intro h
          have h1 : w ∈ S ∩ N w := Finset.mem_inter.2 ⟨hwS, hwN⟩
          have h2 : w' ∈ S ∩ N w := Finset.mem_inter.2 ⟨h, hw'N⟩
          rw [hz, Finset.mem_singleton] at h1 h2
          exact hww' (h1.trans h2.symm)
        rw [← hφ, Finset.erase_insert hw'S]
      · right
        simp only [φ, if_neg hwS] at hφ
        rw [← hφ, Finset.erase_insert hwS]
    have hle2 : single.card ≤ 2 * multi.card :=
      Finset.card_le_mul_card_image_of_maps_to hmaps 2 (fun M _ => hfib M)
    omega
  have hEsum : ∀ w, ∑ x ∈ Finset.univ.erase v, (E w x).card ≤
      (D.filter (fun S => (S ∩ N w).card = 1)).card := by
    intro w
    rw [← Finset.card_biUnion]
    · apply Finset.card_le_card
      intro S hS
      obtain ⟨x, -, hx⟩ := Finset.mem_biUnion.1 hS
      rw [hE, Finset.mem_filter] at hx
      rw [Finset.mem_filter, hx.2, Finset.card_singleton]
      exact ⟨hx.1, rfl⟩
    · intro x _ y _ hxy
      rw [Function.onFun, Finset.disjoint_left]
      intro S hSx hSy
      rw [hE, Finset.mem_filter] at hSx hSy
      exact hxy (Finset.singleton_injective (hSx.2.symm.trans hSy.2))
  have hcsum : 3 * ∑ x, c x ≤ 3 * D.card + 2 * U.card * D.card := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
    have hcv : c v ≤ D.card := Finset.card_filter_le _ _
    have h1 : ∑ x ∈ Finset.univ.erase v, c x ≤ ∑ w ∈ U, (D.filter (fun S => (S ∩ N w).card = 1)).card := by
      calc ∑ x ∈ Finset.univ.erase v, c x
          ≤ ∑ x ∈ Finset.univ.erase v, ∑ w ∈ U, (E w x).card :=
            Finset.sum_le_sum fun x hx => hcrit x (Finset.ne_of_mem_erase hx)
        _ = ∑ w ∈ U, ∑ x ∈ Finset.univ.erase v, (E w x).card := Finset.sum_comm
        _ ≤ _ := Finset.sum_le_sum fun w _ => hEsum w
    have h2 : 3 * ∑ w ∈ U, (D.filter (fun S => (S ∩ N w).card = 1)).card ≤ 2 * U.card * D.card := by
      rw [Finset.mul_sum]
      calc ∑ w ∈ U, 3 * (D.filter (fun S => (S ∩ N w).card = 1)).card
          ≤ ∑ w ∈ U, 2 * D.card := Finset.sum_le_sum fun w _ => hthird w
        _ = 2 * U.card * D.card := by rw [Finset.sum_const, smul_eq_mul]; ring
    omega
  have h2a : 2 * ∑ x, a x = n * D.card + ∑ x, c x := by
    have e1 : ∑ x, (a x + b x) = n * D.card := by
      rw [Finset.sum_congr rfl fun x _ => hab x, Finset.sum_const, smul_eq_mul, Finset.card_univ]
    have e2 : ∑ x, a x = ∑ x, b x + ∑ x, c x := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun x _ => habc x
    rw [← e1, Finset.sum_add_distrib]; omega
  -- conclude
  have hm : U.card + G.degree v + 1 = n := by rw [hUcard]; omega
  have hDpos : (0 : ℚ) < D.card := by exact_mod_cast hDne.card_pos
  have qa : (2 : ℚ) * ((∑ x, a x : ℕ) : ℚ) = n * D.card + ((∑ x, c x : ℕ) : ℚ) := by
    exact_mod_cast h2a
  have qc : (3 : ℚ) * ((∑ x, c x : ℕ) : ℚ) ≤ 3 * D.card + 2 * U.card * D.card := by
    exact_mod_cast hcsum
  have qm : (U.card : ℚ) + G.degree v + 1 = n := by exact_mod_cast hm
  have qs : ∑ S ∈ D, (S.card : ℚ) = ((∑ x, a x : ℕ) : ℚ) := by rw [← hsum, Nat.cast_sum]
  have qnD : (n : ℚ) * D.card = U.card * D.card + G.degree v * D.card + D.card := by
    rw [← qm]; ring
  unfold simple_graph_local_avg_dominating_order
  rw [← hD, div_le_div_iff₀ hDpos (by norm_num : (0 : ℚ) < 6), qs]
  linarith
