import AFTD.Prelude
import AFTD.Kb.Tcs.IsMinimallyKExtendable
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.MatchingShortAlternatingCycleNearUniversal
import AFTD.Kb.Tcs.MatchingBlockedShortSwitchesTwoMissingSaturation
import AFTD.Kb.Tcs.MinimallyKExtendableOrderTwoMulAddEightLowCodegreeDegreeBound

/-!
# minimally_k_extendable_order_two_mul_add_eight_dense_complement_neighborhood_bound

Topic: graphs   Node: 5fca7846ed62

Provenance: helper lemma. OP-1957: dense complement-neighborhood selection route at order 2k+8; local obstruction models tested in experiment 34586.

A minimally k-extendable graph on 2k+8 vertices, k at least four, has minimum degree at most 2k+1 if the complement has a degree-four vertex with at least three edges in its neighborhood or a degree-five vertex with at least six edges in its neighborhood.
-/

theorem in1162d_double_count {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
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

theorem in1162d_codeg_ncard {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p z : Fin n) (S : Finset (Fin n)) (hS : (Gᶜ).neighborFinset p = S) :
    ({x | (Gᶜ).Adj p x ∧ (Gᶜ).Adj z x} : Set (Fin n)).ncard =
      (S.filter (fun y => (Gᶜ).Adj z y)).card := by
  classical
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp [← hS]

theorem minimally_k_extendable_order_two_mul_add_eight_dense_complement_neighborhood_bound
    (k : ℕ) (hk : 4 ≤ k) (G : SimpleGraph (Fin (2*k+8))) [DecidableRel G.Adj]
    (hmin : is_minimally_k_extendable G k) (u : Fin (2*k+8))
    (hdense : ((Gᶜ).degree u = 4 ∧ 3 ≤ ({e : Sym2 (Fin (2*k+8)) | ∃ a b, e = s(a,b) ∧ (Gᶜ).Adj u a ∧ (Gᶜ).Adj u b ∧ (Gᶜ).Adj a b} : Set (Sym2 (Fin (2*k+8)))).ncard) ∨
              ((Gᶜ).degree u = 5 ∧ 6 ≤ ({e : Sym2 (Fin (2*k+8)) | ∃ a b, e = s(a,b) ∧ (Gᶜ).Adj u a ∧ (Gᶜ).Adj u b ∧ (Gᶜ).Adj a b} : Set (Sym2 (Fin (2*k+8)))).ncard)) :
    G.minDegree ≤ 2*k+1 := open SimpleGraph in by
  classical
  by_contra hlt
  have hH : ∀ x, (Gᶜ).degree x ≤ 5 := by
    intro x
    have h1 := G.degree_compl x
    have h2 := G.minDegree_le_degree x
    rw [Fintype.card_fin] at h1
    omega
  have hedge : ∃ a b, (Gᶜ).Adj u a ∧ (Gᶜ).Adj u b ∧ (Gᶜ).Adj a b := by
    have hne : ({e : Sym2 (Fin (2*k+8)) | ∃ a b, e = s(a,b) ∧ (Gᶜ).Adj u a ∧ (Gᶜ).Adj u b ∧
        (Gᶜ).Adj a b} : Set (Sym2 (Fin (2*k+8)))).Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by rcases hdense with h | h <;> omega)
    obtain ⟨e, a, b, -, ha, hb, hab⟩ := hne
    exact ⟨a, b, ha, hb, hab⟩
  obtain ⟨a0, b0, ha0, hb0, hab0⟩ := hedge
  set N := (Gᶜ).neighborFinset u with hNdef
  have hNc : N.card ≤ 5 := by rw [hNdef, card_neighborFinset_eq_degree]; exact hH u
  have huN : u ∉ N := by rw [hNdef, mem_neighborFinset]; exact (Gᶜ).loopless.irrefl u
  have ha0N : a0 ∈ N := by rw [hNdef, mem_neighborFinset]; exact ha0
  have hb0N : b0 ∈ N := by rw [hNdef, mem_neighborFinset]; exact hb0
  have hab : a0 ≠ b0 := hab0.ne
  set W := Finset.univ \ insert u N with hW
  have hWc : W.card + N.card = 2*k+7 := by
    rw [hW, Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ,
      Finset.card_insert_of_notMem huN]
    omega
  set f : Fin (2*k+8) → ℕ := fun a => (W.filter (fun z => (Gᶜ).Adj a z)).card with hf
  have hf4 : ∀ a ∈ N, f a ≤ 4 := by
    intro a ha
    have hua : (Gᶜ).Adj a u := ((mem_neighborFinset _ _ _).1 (hNdef ▸ ha)).symm
    have hsub : W.filter (fun z => (Gᶜ).Adj a z) ⊆ ((Gᶜ).neighborFinset a).erase u := by
      intro z hz
      rw [Finset.mem_filter, hW, Finset.mem_sdiff] at hz
      simp only [Finset.mem_insert, not_or] at hz
      rw [Finset.mem_erase, mem_neighborFinset]
      exact ⟨hz.1.2.1, hz.2⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (by rw [mem_neighborFinset]; exact hua),
      card_neighborFinset_eq_degree] at h1
    have := hH a
    simp only [hf]
    omega
  have hf3 : ∀ a b, (Gᶜ).Adj u a → (Gᶜ).Adj a b → b ∈ N → f a ≤ 3 := by
    intro a b ha hab' hbN
    have hua : (Gᶜ).Adj a u := ha.symm
    have hsub : W.filter (fun z => (Gᶜ).Adj a z) ⊆ (((Gᶜ).neighborFinset a).erase u).erase b := by
      intro z hz
      rw [Finset.mem_filter, hW, Finset.mem_sdiff] at hz
      simp only [Finset.mem_insert, not_or] at hz
      rw [Finset.mem_erase, Finset.mem_erase, mem_neighborFinset]
      exact ⟨fun h => hz.1.2.2 (h ▸ hbN), hz.1.2.1, hz.2⟩
    have h1 := Finset.card_le_card hsub
    have hbu : b ≠ u := fun h => huN (h ▸ hbN)
    rw [Finset.card_erase_of_mem (by rw [Finset.mem_erase, mem_neighborFinset]; exact ⟨hbu, hab'⟩),
      Finset.card_erase_of_mem (by rw [mem_neighborFinset]; exact hua),
      card_neighborFinset_eq_degree] at h1
    have := hH a
    simp only [hf]
    omega
  have hsum : ∑ a ∈ N, f a + 2 ≤ 4 * N.card := by
    have e1 := Finset.add_sum_erase N f ha0N
    have hb0' : b0 ∈ N.erase a0 := Finset.mem_erase.2 ⟨hab.symm, hb0N⟩
    have e2 := Finset.add_sum_erase (N.erase a0) f hb0'
    have hrest : ∑ a ∈ (N.erase a0).erase b0, f a ≤ ((N.erase a0).erase b0).card • 4 :=
      Finset.sum_le_card_nsmul _ _ _ (fun a ha =>
        hf4 a (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ha)))
    rw [smul_eq_mul, Finset.card_erase_of_mem hb0', Finset.card_erase_of_mem ha0N] at hrest
    have h3a := hf3 a0 b0 ha0 hab0 hb0N
    have h3b := hf3 b0 a0 hb0 hab0.symm ha0N
    have hN2 : 2 ≤ N.card := by
      have := Finset.card_le_card (show {a0, b0} ⊆ N by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption)
      rwa [Finset.card_pair hab] at this
    have : N.card - 1 - 1 = N.card - 2 := by omega
    rw [this] at hrest
    have : (N.card - 2) * 4 + 8 = 4 * N.card := by
      have : N.card = (N.card - 2) + 2 := by omega
      rw [this]; ring_nf; omega
    omega
  have hbad := in1162d_double_count (Gᶜ) N W (4 * N.card - 2) (by simp only [hf] at hsum; omega)
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := W) (fun z => 2 ≤ (N.filter (fun y => (Gᶜ).Adj z y)).card)
  have hgood : 0 < (W.filter (fun z => ¬ 2 ≤ (N.filter (fun y => (Gᶜ).Adj z y)).card)).card := by
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hgood
  rw [Finset.mem_filter, hW, Finset.mem_sdiff] at hw
  simp only [Finset.mem_insert, not_or] at hw
  obtain ⟨⟨-, hwu, hwN⟩, hwc⟩ := hw
  have huw : G.Adj u w := by
    by_contra hn
    apply hwN
    rw [hNdef, mem_neighborFinset, compl_adj]
    exact ⟨fun h => hwu h.symm, hn⟩
  have hcw : ({x | (Gᶜ).Adj u x ∧ (Gᶜ).Adj w x} : Set (Fin (2*k+8))).ncard ≤ 1 := by
    rw [in1162d_codeg_ncard G u w N rfl]
    omega
  exact hlt (minimally_k_extendable_order_two_mul_add_eight_low_codegree_degree_bound k hk G hmin
    ⟨u, w, huw, hcw⟩)
