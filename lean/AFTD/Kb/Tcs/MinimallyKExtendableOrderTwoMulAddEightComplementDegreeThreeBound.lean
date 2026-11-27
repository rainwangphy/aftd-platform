import AFTD.Prelude
import AFTD.Kb.Tcs.IsMinimallyKExtendable
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.MatchingBlockedShortSwitchesTwoMissingSaturation
import AFTD.Kb.Tcs.MatchingShortSwitchComplementLocalGirthFive
import AFTD.Kb.Tcs.MinimallyKExtendableComplementDegreeTwoBound
import AFTD.Kb.Tcs.MinimallyKExtendableOrderTwoMulAddEightDenseComplementNeighborhoodBound
import AFTD.Kb.Tcs.MinimallyKExtendableOrderTwoMulAddEightLowCodegreeDegreeBound

/-!
# minimally_k_extendable_order_two_mul_add_eight_complement_degree_three_bound

Topic: graphs   Node: 676f96a64eab

Provenance: helper lemma. OP-1957: degree-three complement reduction for the 2k+8 order; general proof plan not yet checked by Lean.

A minimally k-extendable graph on 2k+8 vertices, for k at least four, has minimum degree at most 2k+1 if some vertex has at most three nonneighbors.
-/

theorem minimally_k_extendable_order_two_mul_add_eight_complement_degree_three_bound
    (k : ℕ) (hk : 4 ≤ k) (G : SimpleGraph (Fin (2*k+8))) [DecidableRel G.Adj]
    (hmin : is_minimally_k_extendable G k) (u : Fin (2*k+8))
    (hu : (Gᶜ).degree u ≤ 3) : G.minDegree ≤ 2*k+1 := open SimpleGraph in by
  classical
  by_contra hlt
  have hH : ∀ x, (Gᶜ).degree x ≤ 5 := by
    intro x
    have h1 := G.degree_compl x
    have h2 := G.minDegree_le_degree x
    rw [Fintype.card_fin] at h1
    omega
  set N := (Gᶜ).neighborFinset u with hNdef
  have hNc : N.card ≤ 3 := by rw [hNdef, card_neighborFinset_eq_degree]; exact hu
  have huN : u ∉ N := by rw [hNdef, mem_neighborFinset]; exact (Gᶜ).loopless.irrefl u
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
  have hsum : ∑ a ∈ N, f a ≤ 4 * N.card := by
    have hrest : ∑ a ∈ N, f a ≤ N.card • 4 := Finset.sum_le_card_nsmul _ _ _ hf4
    rw [smul_eq_mul] at hrest
    omega
  have hbad := in1162d_double_count (Gᶜ) N W (4 * N.card) (by simp only [hf] at hsum; exact hsum)
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
