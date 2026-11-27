import AFTD.Prelude
import AFTD.Kb.Tcs.IsMinimallyKExtendable
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.KExtendableOrderTwoMulAddEightTwinLowCodegreeOneRemovable

/-!
# minimally_k_extendable_order_two_mul_add_eight_low_codegree_degree_bound

Topic: graphs   Node: 6f1deefc1750

Provenance: helper lemma. OP-1957: low-codegree edge gives saturated complement twins, then the twin-pair degree-budget contradiction.

A minimally k-extendable graph on 2k+8 vertices, k at least four, has minimum degree at most 2k+1 whenever it has an edge whose endpoints have at most one common nonneighbor.
-/

open SimpleGraph in
theorem in1162_twins_of_sides {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hH : ∀ x, (Gᶜ).degree x ≤ 5)
    (X Y : Finset (Fin n)) (x y : Fin n) (hx : x ∈ X)
    (hX : X.card = 3) (hY : Y.card = 5)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, (a = x ∧ b = y) ∨ (Gᶜ).Adj a b) :
    ∃ p q, p ≠ q ∧ (Gᶜ).neighborFinset p = Y ∧ (Gᶜ).neighborFinset q = Y := by
  classical
  have h2 : (X.erase x).card = 2 := by rw [Finset.card_erase_of_mem hx, hX]
  obtain ⟨p, q, hpq, he⟩ := Finset.card_eq_two.mp h2
  have key : ∀ p ∈ X.erase x, (Gᶜ).neighborFinset p = Y := by
    intro p hp
    have hpX := Finset.mem_of_mem_erase hp
    have hpx := Finset.ne_of_mem_erase hp
    have hsub : Y ⊆ (Gᶜ).neighborFinset p := fun b hb =>
      (mem_neighborFinset _ _ _).2 ((hcross p hpX b hb).resolve_left (fun h => hpx h.1))
    exact (Finset.eq_of_subset_of_card_le hsub
      (by rw [card_neighborFinset_eq_degree, hY]; exact hH p)).symm
  exact ⟨p, q, hpq, key p (by rw [he]; simp), key q (by rw [he]; simp)⟩

theorem in1162_double_count {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (S Z : Finset (Fin n)) (c : ℕ)
    (hsum : ∑ y ∈ S, (Z.filter (fun z => H.Adj y z)).card ≤ c) :
    2 * (Z.filter (fun z => 2 ≤ (S.filter (fun y => H.Adj z y)).card)).card ≤ c := by
  classical
  have hbip := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := Z) (t := S) (r := fun z y => H.Adj z y)
  have hL : ∑ z ∈ Z, (S.filter (fun y => H.Adj z y)).card ≤ c := by
    have e1 : ∑ z ∈ Z, (S.filter (fun y => H.Adj z y)).card =
        ∑ z ∈ Z, (S.bipartiteAbove (fun z y => H.Adj z y) z).card := by
      rfl
    have e2 : ∑ y ∈ S, (Z.bipartiteBelow (fun z y => H.Adj z y) y).card =
        ∑ y ∈ S, (Z.filter (fun z => H.Adj y z)).card := by
      apply Finset.sum_congr rfl
      intro y _
      congr 1
      ext z
      simp [Finset.bipartiteBelow, H.adj_comm]
    rw [e1, hbip, e2]
    exact hsum
  set bad := Z.filter (fun z => 2 ≤ (S.filter (fun y => H.Adj z y)).card)
  have h1 : bad.card • 2 ≤ ∑ z ∈ bad, (S.filter (fun y => H.Adj z y)).card :=
    Finset.card_nsmul_le_sum _ _ _ (fun z hz => (Finset.mem_filter.1 hz).2)
  have h2 : ∑ z ∈ bad, (S.filter (fun y => H.Adj z y)).card ≤
      ∑ z ∈ Z, (S.filter (fun y => H.Adj z y)).card :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  rw [smul_eq_mul] at h1
  omega

theorem in1162_codeg_ncard {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p z : Fin n) (S : Finset (Fin n)) (hS : (Gᶜ).neighborFinset p = S) :
    ({x | (Gᶜ).Adj p x ∧ (Gᶜ).Adj z x} : Set (Fin n)).ncard =
      (S.filter (fun y => (Gᶜ).Adj z y)).card := by
  classical
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp [← hS]

open SimpleGraph in
theorem in1162_twin_two_neighbors (k : ℕ) (hk : 4 ≤ k) (G : SimpleGraph (Fin (2*k+8)))
    [DecidableRel G.Adj] (hH : ∀ x, (Gᶜ).degree x ≤ 5)
    (p q : Fin (2*k+8)) (Y : Finset (Fin (2*k+8))) (hpq : p ≠ q) (hY : Y.card = 5)
    (hp : (Gᶜ).neighborFinset p = Y) (hq : (Gᶜ).neighborFinset q = Y) :
    ∃ v w, G.Adj p v ∧ G.Adj p w ∧ v ≠ q ∧ w ≠ q ∧ v ≠ w ∧
      ({x | (Gᶜ).Adj p x ∧ (Gᶜ).Adj v x} : Set (Fin (2*k+8))).ncard ≤ 1 ∧
      ({x | (Gᶜ).Adj p x ∧ (Gᶜ).Adj w x} : Set (Fin (2*k+8))).ncard ≤ 1 := by
  classical
  have hpY : p ∉ Y := by rw [← hp, mem_neighborFinset]; exact (Gᶜ).loopless.irrefl p
  have hqY : q ∉ Y := by rw [← hq, mem_neighborFinset]; exact (Gᶜ).loopless.irrefl q
  set Z := Finset.univ \ (insert p (insert q Y)) with hZ
  have hZc : Z.card = 2*k+1 := by
    rw [hZ, Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ,
      Finset.card_insert_of_notMem (by simp [hpq, hpY]), Finset.card_insert_of_notMem hqY, hY]
    omega
  have hsum : ∑ y ∈ Y, (Z.filter (fun z => (Gᶜ).Adj y z)).card ≤ 15 := by
    have : ∑ y ∈ Y, (Z.filter (fun z => (Gᶜ).Adj y z)).card ≤ Y.card • 3 := by
      apply Finset.sum_le_card_nsmul
      intro y hy
      have hpy : (Gᶜ).Adj y p := by
        have : y ∈ (Gᶜ).neighborFinset p := hp ▸ hy
        exact ((mem_neighborFinset _ _ _).1 this).symm
      have hqy : (Gᶜ).Adj y q := by
        have : y ∈ (Gᶜ).neighborFinset q := hq ▸ hy
        exact ((mem_neighborFinset _ _ _).1 this).symm
      have hsub : Z.filter (fun z => (Gᶜ).Adj y z) ⊆ (((Gᶜ).neighborFinset y).erase p).erase q := by
        intro z hz
        rw [Finset.mem_filter, hZ, Finset.mem_sdiff] at hz
        simp only [Finset.mem_insert, not_or] at hz
        rw [Finset.mem_erase, Finset.mem_erase, mem_neighborFinset]
        exact ⟨hz.1.2.2.1, hz.1.2.1, hz.2⟩
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (by rw [Finset.mem_erase, mem_neighborFinset]; exact ⟨hpq.symm, hqy⟩),
        Finset.card_erase_of_mem (by rw [mem_neighborFinset]; exact hpy),
        card_neighborFinset_eq_degree] at h1
      have := hH y
      omega
    rw [smul_eq_mul, hY] at this
    exact this
  have hbad := in1162_double_count (Gᶜ) Y Z 15 hsum
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Z) (fun z => 2 ≤ (Y.filter (fun y => (Gᶜ).Adj z y)).card)
  have hgood : 1 < (Z.filter (fun z => ¬ 2 ≤ (Y.filter (fun y => (Gᶜ).Adj z y)).card)).card := by
    omega
  obtain ⟨v, hv, w, hw, hvw⟩ := Finset.one_lt_card.mp hgood
  have hmem : ∀ z ∈ Z.filter (fun z => ¬ 2 ≤ (Y.filter (fun y => (Gᶜ).Adj z y)).card),
      G.Adj p z ∧ z ≠ q ∧
      ({x | (Gᶜ).Adj p x ∧ (Gᶜ).Adj z x} : Set (Fin (2*k+8))).ncard ≤ 1 := by
    intro z hz
    rw [Finset.mem_filter, hZ, Finset.mem_sdiff] at hz
    simp only [Finset.mem_insert, not_or] at hz
    obtain ⟨⟨-, hzp, hzq, hzY⟩, hzc⟩ := hz
    refine ⟨?_, hzq, ?_⟩
    · by_contra hn
      apply hzY
      rw [← hp, mem_neighborFinset, compl_adj]
      exact ⟨fun h => hzp h.symm, hn⟩
    · rw [in1162_codeg_ncard G p z Y hp]
      omega
  obtain ⟨hv1, hv2, hv3⟩ := hmem v hv
  obtain ⟨hw1, hw2, hw3⟩ := hmem w hw
  exact ⟨v, w, hv1, hw1, hv2, hw2, hvw, hv3, hw3⟩

theorem minimally_k_extendable_order_two_mul_add_eight_low_codegree_degree_bound
    (k : ℕ) (hk : 4 ≤ k) (G : SimpleGraph (Fin (2*k+8))) [DecidableRel G.Adj]
    (hmin : is_minimally_k_extendable G k)
    (hco : ∃ u v, G.Adj u v ∧ ({x | (Gᶜ).Adj u x ∧ (Gᶜ).Adj v x} : Set (Fin (2*k+8))).ncard ≤ 1) :
    G.minDegree ≤ 2*k+1 := open SimpleGraph in by
  classical
  by_contra hlt
  have hdeg : 2*k+2 ≤ G.minDegree := by omega
  have hH : ∀ x, (Gᶜ).degree x ≤ 5 := by
    intro x
    have h1 := G.degree_compl x
    have h2 := G.minDegree_le_degree x
    rw [Fintype.card_fin] at h1
    omega
  obtain ⟨u, v, huv, hc⟩ := hco
  have hnot : ¬ is_k_extendable (G.deleteEdges {s(u,v)}) k := hmin.2 _ huv
  have hc' : (((Gᶜ).neighborFinset u).filter (fun w => (Gᶜ).Adj v w)).card < 2 := by
    rw [← in1162_codeg_ncard G u v _ rfl]
    omega
  obtain ⟨A, B, -, huA, hvB, hcard, hoA, hoB, hA, hB, hcross⟩ :=
    in1069_bridge k (2*k+8) 2 le_rfl G u v huv hmin.1 hnot hdeg hc'
  have htw : ∃ p q Y, p ≠ q ∧ Y.card = 5 ∧ (Gᶜ).neighborFinset p = Y ∧
      (Gᶜ).neighborFinset q = Y := by
    obtain ⟨m1, hm1⟩ := hoA
    obtain ⟨m2, hm2⟩ := hoB
    by_cases h3 : A.card = 3
    · obtain ⟨p, q, hpq, hp, hq⟩ := in1162_twins_of_sides G hH A B u v huA h3 (by omega) hcross
      exact ⟨p, q, B, hpq, by omega, hp, hq⟩
    · have hB3 : B.card = 3 := by omega
      obtain ⟨p, q, hpq, hp, hq⟩ := in1162_twins_of_sides G hH B A v u hvB hB3 (by omega)
        (fun a ha b hb => by
          rcases hcross b hb a ha with ⟨h1, h2⟩ | h
          · exact Or.inl ⟨h2, h1⟩
          · exact Or.inr h.symm)
      exact ⟨p, q, A, hpq, by omega, hp, hq⟩
  obtain ⟨p, q, Y, hpq, hY, hp, hq⟩ := htw
  obtain ⟨v1, w1, hv1, hw1, hv1q, hw1q, hvw, hcv, hcw⟩ :=
    in1162_twin_two_neighbors k hk G hH p q Y hpq hY hp hq
  have hpdeg : (Gᶜ).degree p = 5 := by rw [← card_neighborFinset_eq_degree, hp, hY]
  have htwin : ∀ x, (Gᶜ).Adj p x ↔ (Gᶜ).Adj q x := by
    intro x
    rw [← mem_neighborFinset, ← mem_neighborFinset, hp, hq]
  rcases k_extendable_order_two_mul_add_eight_twin_low_codegree_one_removable k hk G hmin.1 hdeg
      p q v1 w1 hpq hpdeg htwin hv1 hw1 hv1q hw1q hvw hcv hcw with h | h
  · exact hmin.2 _ hv1 h
  · exact hmin.2 _ hw1 h
