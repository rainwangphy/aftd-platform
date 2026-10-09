import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphLocalAvgDominatingOrder
import AFTD.Kb.Tcs.SimpleGraphDominatingSetsContaining

/-!
# simple_graph_local_avg_dominating_order_lt_of_four_le

Topic: graphs   Node: 35ee92aeefc5

Provenance: original. Related work: arXiv:2610.11446 (On the local average order of dominating sets), list entry OP-135 (sharpness of the bound (5n−1)/6 of Theorem 3.8 for n ≥ 4); the negation of sharpness. It follows from the conjectured bound (2n+1)/3 (simple_graph_local_avg_dominating_order_le_two_mul_add_one_div_three), which is below (5n−1)/6 for n ≥ 4.

For n ≥ 4 the upper bound (5n−1)/6 is never attained: if G has order n ≥ 4 and no isolated vertices, then avd_v(G) < (5n−1)/6 for every vertex v.
-/

theorem simple_graph_local_avg_dominating_order_lt_of_four_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hn : 4 ≤ Fintype.card V)
    (hiso : ∀ w, 0 < G.degree w) (v : V) :
    simple_graph_local_avg_dominating_order G v < (5 * (Fintype.card V : ℚ) - 1) / 6 := by
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
  have hsubC : ∀ x, x ≠ v →
      D.filter (fun S => x ∈ S ∧ S.erase x ∉ D) ⊆ U.biUnion (fun w => E w x) := by
    intro x hxv S hS
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
  have hcrit : ∀ x, x ≠ v → c x ≤ ∑ w ∈ U, (E w x).card := fun x hxv =>
    le_trans (Finset.card_le_card (hsubC x hxv)) Finset.card_biUnion_le
  -- a set with two witnesses for the same critical vertex makes this strict
  have hcrit_strict : ∀ x, x ≠ v → ∀ w1 ∈ U, ∀ w2 ∈ U, w1 ≠ w2 → ∀ S, S ∈ E w1 x → S ∈ E w2 x →
      c x + 1 ≤ ∑ w ∈ U, (E w x).card := by
    intro x hxv w1 hw1 w2 hw2 hne S hS1 hS2
    have hU' : U = insert w1 (U.erase w1) := (Finset.insert_erase hw1).symm
    have hbu : U.biUnion (fun w => E w x) = E w1 x ∪ (U.erase w1).biUnion (fun w => E w x) := by
      conv_lhs => rw [hU']
      rw [Finset.biUnion_insert]
    have hS' : S ∈ E w1 x ∩ (U.erase w1).biUnion (fun w => E w x) :=
      Finset.mem_inter.2 ⟨hS1, Finset.mem_biUnion.2 ⟨w2, Finset.mem_erase.2 ⟨hne.symm, hw2⟩, hS2⟩⟩
    have h1 := Finset.card_union_add_card_inter (E w1 x) ((U.erase w1).biUnion (fun w => E w x))
    have h2 : 1 ≤ (E w1 x ∩ (U.erase w1).biUnion (fun w => E w x)).card :=
      Finset.card_pos.2 ⟨S, hS'⟩
    have h3 := Finset.card_biUnion_le (s := U.erase w1) (t := fun w => E w x)
    have h4 := Finset.add_sum_erase U (fun w => (E w x).card) hw1
    have h5 : c x ≤ (U.biUnion (fun w => E w x)).card := Finset.card_le_card (hsubC x hxv)
    rw [hbu] at h5
    omega
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
  -- a neighbourhood with three vertices: the whole vertex set is no image, so it is strict
  have hthird_strict : ∀ w, 2 ≤ G.degree w →
      3 * (D.filter (fun S => (S ∩ N w).card = 1)).card + 2 ≤ 2 * D.card := by
    intro w hw2
    obtain ⟨w', hw'⟩ : ∃ w', G.Adj w w' := by
      have := hiso w
      rw [← G.card_neighborFinset_eq_degree, Finset.card_pos] at this
      obtain ⟨w', hw'⟩ := this
      exact ⟨w', (G.mem_neighborFinset w w').1 hw'⟩
    have hww' : w ≠ w' := G.ne_of_adj hw'
    have hwN : w ∈ N w := by simp [hN]
    have hw'N : w' ∈ N w := by simp [hN, G.mem_neighborFinset, hw']
    -- two distinct neighbours of `w`
    have hnb : ∀ z, ∃ y, G.Adj w y ∧ y ≠ z := by
      intro z
      by_contra hcon
      push_neg at hcon
      have : G.neighborFinset w ⊆ {z} := fun y hy =>
        Finset.mem_singleton.2 (hcon y ((G.mem_neighborFinset w y).1 hy))
      have := Finset.card_le_card this
      rw [G.card_neighborFinset_eq_degree, Finset.card_singleton] at this
      omega
    set single := D.filter (fun S => (S ∩ N w).card = 1) with hsingle
    set multi := D.filter (fun S => ¬ (S ∩ N w).card = 1) with hmulti
    have hsm : single.card + multi.card = D.card := Finset.card_filter_add_card_filter_not _
    have huniv : Finset.univ ∈ multi := by
      rw [hmulti, Finset.mem_filter]
      refine ⟨(memD _).2 ⟨Finset.mem_univ v, fun w => Or.inl (Finset.mem_univ w)⟩, fun h1 => ?_⟩
      exact hww' (Finset.card_le_one.1 h1.le w (by simp [hwN]) w' (by simp [hw'N]))
    let φ : Finset V → Finset V := fun S => if w ∈ S then insert w' S else insert w S
    have hmaps : ∀ S ∈ single, φ S ∈ multi.erase Finset.univ := by
      intro S hS
      rw [hsingle, Finset.mem_filter, Finset.card_eq_one] at hS
      obtain ⟨hSD, z, hz⟩ := hS
      rw [Finset.mem_erase, hmulti, Finset.mem_filter]
      by_cases hwS : w ∈ S
      · simp only [φ, if_pos hwS]
        refine ⟨fun hU => ?_, hup S hSD _ (Finset.subset_insert _ _), fun h1 => ?_⟩
        · obtain ⟨y, hy, hyw'⟩ := hnb w'
          have hyS : y ∈ S := by
            have : y ∈ insert w' S := hU ▸ Finset.mem_univ y
            rcases Finset.mem_insert.1 this with h | h
            · exact absurd h hyw'
            · exact h
          have h1 : w ∈ S ∩ N w := Finset.mem_inter.2 ⟨hwS, hwN⟩
          have h2 : y ∈ S ∩ N w := Finset.mem_inter.2 ⟨hyS, by simp [hN, G.mem_neighborFinset, hy]⟩
          rw [hz, Finset.mem_singleton] at h1 h2
          exact G.ne_of_adj hy (h1.trans h2.symm)
        · have hw_in : w ∈ insert w' S ∩ N w :=
            Finset.mem_inter.2 ⟨Finset.mem_insert_of_mem hwS, hwN⟩
          have hw'_in : w' ∈ insert w' S ∩ N w :=
            Finset.mem_inter.2 ⟨Finset.mem_insert_self _ _, hw'N⟩
          exact hww' (Finset.card_le_one.1 h1.le w hw_in w' hw'_in)
      · simp only [φ, if_neg hwS]
        have hz_in : z ∈ S ∩ N w := by rw [hz]; exact Finset.mem_singleton_self z
        have hzw : z ≠ w := fun h => hwS (h ▸ (Finset.mem_inter.1 hz_in).1)
        refine ⟨fun hU => ?_, hup S hSD _ (Finset.subset_insert _ _), fun h1 => ?_⟩
        · -- two neighbours of `w` other than... at least one differs from `z`
          obtain ⟨y, hy, hyz⟩ := hnb z
          have hyS : y ∈ S := by
            have : y ∈ insert w S := hU ▸ Finset.mem_univ y
            rcases Finset.mem_insert.1 this with h | h
            · exact absurd h (G.ne_of_adj hy).symm
            · exact h
          have h2 : y ∈ S ∩ N w := Finset.mem_inter.2 ⟨hyS, by simp [hN, G.mem_neighborFinset, hy]⟩
          rw [hz, Finset.mem_singleton] at h2
          exact hyz h2
        · have hw_in : w ∈ insert w S ∩ N w :=
            Finset.mem_inter.2 ⟨Finset.mem_insert_self _ _, hwN⟩
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
    have hle2 : single.card ≤ 2 * (multi.erase Finset.univ).card :=
      Finset.card_le_mul_card_image_of_maps_to hmaps 2 (fun M _ => hfib M)
    rw [Finset.card_erase_of_mem huniv] at hle2
    have : 1 ≤ multi.card := Finset.card_pos.2 ⟨_, huniv⟩
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
  -- the strict count, in the two cases
  have hcsum_strict : ((∃ w ∈ U, 2 ≤ G.degree w) ∨
      (∃ x, x ≠ v ∧ ∃ w1 ∈ U, ∃ w2 ∈ U, w1 ≠ w2 ∧ ∃ S, S ∈ E w1 x ∧ S ∈ E w2 x)) →
      3 * ∑ x, c x + 1 ≤ 3 * D.card + 2 * U.card * D.card := by
    intro hcase
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
    have hcv : c v ≤ D.card := Finset.card_filter_le _ _
    have hle1 : ∑ x ∈ Finset.univ.erase v, c x ≤ ∑ x ∈ Finset.univ.erase v, ∑ w ∈ U, (E w x).card :=
      Finset.sum_le_sum fun x hx => hcrit x (Finset.ne_of_mem_erase hx)
    have hle2 : ∑ x ∈ Finset.univ.erase v, ∑ w ∈ U, (E w x).card ≤
        ∑ w ∈ U, (D.filter (fun S => (S ∩ N w).card = 1)).card := by
      rw [Finset.sum_comm]; exact Finset.sum_le_sum fun w _ => hEsum w
    have hle3 : ∑ w ∈ U, 3 * (D.filter (fun S => (S ∩ N w).card = 1)).card ≤
        ∑ w ∈ U, 2 * D.card := Finset.sum_le_sum fun w _ => hthird w
    have hconst : ∑ w ∈ U, 2 * D.card = 2 * U.card * D.card := by
      rw [Finset.sum_const, smul_eq_mul]; ring
    rw [← Finset.mul_sum] at hle3
    rcases hcase with ⟨w0, hw0U, hw0⟩ | ⟨x0, hx0v, w1, hw1, w2, hw2, hne, S, hS1, hS2⟩
    · have hlt : ∑ w ∈ U, 3 * (D.filter (fun S => (S ∩ N w).card = 1)).card <
          ∑ w ∈ U, 2 * D.card :=
        Finset.sum_lt_sum (fun w _ => hthird w) ⟨w0, hw0U, by have := hthird_strict w0 hw0; omega⟩
      rw [← Finset.mul_sum] at hlt
      omega
    · have hlt : ∑ x ∈ Finset.univ.erase v, c x <
          ∑ x ∈ Finset.univ.erase v, ∑ w ∈ U, (E w x).card :=
        Finset.sum_lt_sum (fun x hx => hcrit x (Finset.ne_of_mem_erase hx))
          ⟨x0, Finset.mem_erase.2 ⟨hx0v, Finset.mem_univ x0⟩,
            by have := hcrit_strict x0 hx0v w1 hw1 w2 hw2 hne S hS1 hS2; omega⟩
      omega
  have h2a : 2 * ∑ x, a x = n * D.card + ∑ x, c x := by
    have e1 : ∑ x, (a x + b x) = n * D.card := by
      rw [Finset.sum_congr rfl fun x _ => hab x, Finset.sum_const, smul_eq_mul, Finset.card_univ]
    have e2 : ∑ x, a x = ∑ x, b x + ∑ x, c x := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun x _ => habc x
    rw [← e1, Finset.sum_add_distrib]; omega
  have hDpos : (0 : ℚ) < D.card := by exact_mod_cast hDne.card_pos
  have qs : ∑ S ∈ D, (S.card : ℚ) = ((∑ x, a x : ℕ) : ℚ) := by rw [← hsum, Nat.cast_sum]
  have qa : (2 : ℚ) * ((∑ x, a x : ℕ) : ℚ) = n * D.card + ((∑ x, c x : ℕ) : ℚ) := by
    exact_mod_cast h2a
  have hdv : 1 ≤ G.degree v := hiso v
  have hm : U.card + G.degree v + 1 = n := by rw [hUcard]; omega
  have qm : (U.card : ℚ) + G.degree v + 1 = n := by exact_mod_cast hm
  unfold simple_graph_local_avg_dominating_order
  rw [← hD, div_lt_div_iff₀ hDpos (by norm_num : (0 : ℚ) < 6), qs]
  by_cases hdeg2 : 2 ≤ G.degree v
  · -- the bound `(5n - 2 deg v + 1)/6` is already below `(5n - 1)/6`
    have qc : (3 : ℚ) * ((∑ x, c x : ℕ) : ℚ) ≤ 3 * D.card + 2 * U.card * D.card := by
      exact_mod_cast hcsum
    have q2 : (2 : ℚ) ≤ G.degree v := by exact_mod_cast hdeg2
    have qnD : (n : ℚ) * D.card = U.card * D.card + G.degree v * D.card + D.card := by
      rw [← qm]; ring
    nlinarith
  · have hdv1 : G.degree v = 1 := by omega
    -- `v` has a single neighbour `y`
    obtain ⟨y, hy⟩ : ∃ y, G.neighborFinset v = {y} := by
      rw [← Finset.card_eq_one, G.card_neighborFinset_eq_degree, hdv1]
    have hUall : ∀ z, z ∉ U → z = v ∨ z = y := by
      intro z hz
      rw [hU, Finset.mem_sdiff, Finset.mem_erase, hy, Finset.mem_singleton] at hz
      by_cases hzv : z = v
      · exact Or.inl hzv
      · right; by_contra hzy; exact hz ⟨⟨hzv, Finset.mem_univ z⟩, hzy⟩
    have hvU : v ∉ U := by simp [hU]
    have hyU : y ∉ U := by
      rw [hU, Finset.mem_sdiff, hy]; simp
    have hUcard2 : 2 ≤ U.card := by omega
    have hcase : (∃ w ∈ U, 2 ≤ G.degree w) ∨
        (∃ x, x ≠ v ∧ ∃ w1 ∈ U, ∃ w2 ∈ U, w1 ≠ w2 ∧ ∃ S, S ∈ E w1 x ∧ S ∈ E w2 x) := by
      by_cases hα : ∃ w ∈ U, 2 ≤ G.degree w
      · exact Or.inl hα
      right
      push_neg at hα
      -- every vertex of `U` is a leaf
      have hleaf : ∀ w ∈ U, ∃ z, G.neighborFinset w = {z} := by
        intro w hw
        rw [← Finset.card_eq_one, G.card_neighborFinset_eq_degree]
        have := hiso w; have := hα w hw; omega
      have hNw : ∀ w z, G.neighborFinset w = {z} → N w = {w, z} := by
        intro w z h; simp only [hN, h]
      have hwv : ∀ w ∈ U, ∀ z, G.Adj w z → z ≠ v := by
        intro w hw z hz hzv
        rw [hzv] at hz
        rw [hU, Finset.mem_sdiff, G.mem_neighborFinset] at hw
        exact hw.2 hz.symm
      -- a leaf of `U` whose neighbour is in `U`: a `K₂` component
      have hK2 : ∀ w ∈ U, ∀ z, G.neighborFinset w = {z} → z ∈ U →
          ∃ x, x ≠ v ∧ ∃ w1 ∈ U, ∃ w2 ∈ U, w1 ≠ w2 ∧ ∃ S, S ∈ E w1 x ∧ S ∈ E w2 x := by
        intro w hw z hz hzU
        have hwz : G.Adj w z := (G.mem_neighborFinset w z).1 (by rw [hz]; simp)
        obtain ⟨z', hz'⟩ := hleaf z hzU
        have hzw : G.Adj z w := hwz.symm
        have hz'w : z' = w := by
          have : w ∈ G.neighborFinset z := (G.mem_neighborFinset z w).2 hzw
          rw [hz', Finset.mem_singleton] at this; exact this.symm
        have hne : w ≠ z := G.ne_of_adj hwz
        have hSD : Finset.univ.erase z ∈ D := by
          rw [memD]
          refine ⟨Finset.mem_erase.2 ⟨fun h => hvU (h ▸ hzU), Finset.mem_univ v⟩, fun t => ?_⟩
          by_cases htz : t = z
          · exact Or.inr ⟨w, Finset.mem_erase.2 ⟨hne, Finset.mem_univ w⟩, htz ▸ hwz⟩
          · exact Or.inl (Finset.mem_erase.2 ⟨htz, Finset.mem_univ t⟩)
        refine ⟨w, fun h => hvU (h ▸ hw), w, hw, z, hzU, hne, Finset.univ.erase z, ?_, ?_⟩
        · rw [hE, Finset.mem_filter, hNw w z hz]
          refine ⟨hSD, ?_⟩
          ext t; simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ, and_true,
            Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨htz, rfl | rfl⟩
            · rfl
            · exact absurd rfl htz
          · rintro rfl; exact ⟨hne, Or.inl rfl⟩
        · rw [hE, Finset.mem_filter, hNw z w (by rw [hz', hz'w])]
          refine ⟨hSD, ?_⟩
          ext t; simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ, and_true,
            Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨htz, rfl | rfl⟩
            · exact absurd rfl htz
            · rfl
          · rintro rfl; exact ⟨hne, Or.inr rfl⟩
      obtain ⟨w1, hw1⟩ := Finset.card_pos.1 (by omega : 0 < U.card)
      obtain ⟨z1, hz1⟩ := hleaf w1 hw1
      by_cases hz1U : z1 ∈ U
      · exact hK2 w1 hw1 z1 hz1 hz1U
      obtain ⟨w2, hw2, hw21⟩ := Finset.exists_mem_ne (by omega : 1 < U.card) w1
      obtain ⟨z2, hz2⟩ := hleaf w2 hw2
      by_cases hz2U : z2 ∈ U
      · exact hK2 w2 hw2 z2 hz2 hz2U
      have hw1z1 : G.Adj w1 z1 := (G.mem_neighborFinset w1 z1).1 (by rw [hz1]; simp)
      have hw2z2 : G.Adj w2 z2 := (G.mem_neighborFinset w2 z2).1 (by rw [hz2]; simp)
      have hz1y : z1 = y := (hUall z1 hz1U).resolve_left (hwv w1 hw1 z1 hw1z1)
      have hz2y : z2 = y := (hUall z2 hz2U).resolve_left (hwv w2 hw2 z2 hw2z2)
      -- two leaves on `y`: drop both, `y` is critical with both as witnesses
      set S := (Finset.univ.erase w1).erase w2 with hS
      have hw1y : w1 ≠ y := fun h => hyU (h ▸ hw1)
      have hw2y : w2 ≠ y := fun h => hyU (h ▸ hw2)
      have hSD : S ∈ D := by
        rw [memD]
        refine ⟨by simp [hS]; exact ⟨fun h => hvU (h ▸ hw2), fun h => hvU (h ▸ hw1)⟩, fun t => ?_⟩
        by_cases ht1 : t = w1
        · exact Or.inr ⟨y, by simp [hS]; exact ⟨hw2y.symm, hw1y.symm⟩, ht1 ▸ hz1y ▸ hw1z1.symm⟩
        by_cases ht2 : t = w2
        · exact Or.inr ⟨y, by simp [hS]; exact ⟨hw2y.symm, hw1y.symm⟩, ht2 ▸ hz2y ▸ hw2z2.symm⟩
        exact Or.inl (by simp [hS]; exact ⟨ht2, ht1⟩)
      have hmem : ∀ w z, w ∈ U → G.neighborFinset w = {z} → z = y → (w = w1 ∨ w = w2) →
          S ∈ E w y := by
        intro w z _ hz hzy hw
        rw [hE, Finset.mem_filter, hNw w z hz, hzy]
        refine ⟨hSD, ?_⟩
        ext t
        simp only [hS, Finset.mem_inter, Finset.mem_erase, Finset.mem_univ, and_true,
          Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨ht2, ht1⟩, h | h⟩
          · rcases hw with rfl | rfl
            · exact absurd h ht1
            · exact absurd h ht2
          · exact h
        · rintro rfl; exact ⟨⟨hw2y.symm, hw1y.symm⟩, Or.inr rfl⟩
      exact ⟨y, (G.ne_of_adj ((G.mem_neighborFinset v y).1 (by rw [hy]; simp))).symm, w1, hw1, w2, hw2, hw21.symm, S,
        hmem w1 z1 hw1 hz1 hz1y (Or.inl rfl), hmem w2 z2 hw2 hz2 hz2y (Or.inr rfl)⟩
    have qc : (3 : ℚ) * ((∑ x, c x : ℕ) : ℚ) + 1 ≤ 3 * D.card + 2 * U.card * D.card := by
      exact_mod_cast hcsum_strict hcase
    have q1 : (G.degree v : ℚ) = 1 := by exact_mod_cast hdv1
    have qnD : (n : ℚ) * D.card = U.card * D.card + G.degree v * D.card + D.card := by
      rw [← qm]; ring
    nlinarith
