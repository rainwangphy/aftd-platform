import AFTD.Prelude
import AFTD.Kb.Tcs.FactorCriticalAnticompleteCutSideEven
import AFTD.Kb.Tcs.IsKFactorCritical

/-!
# factorcritical_even_shore_forces_hub_in_opposite_shore

Topic: graphs   Node: 7484759e7c4b

Provenance: helper lemma. OP-1957 first-star-cut branch: a four-shore and its opposite shore otherwise create an odd anticomplete residual.

In a 2k-factor-critical complement graph, suppose an even shore W of at least two vertices is cross-complete in H to Q with |Q|+|W|=d+1, and every shore vertex is adjacent in H to x,y and, except possibly one vertex, u. If x,y,u are distinct, x,y are outside Q and u is outside W, then u lies in Q.
-/

theorem factorcritical_even_shore_forces_hub_in_opposite_shore (k d : ℕ) (H : SimpleGraph (Fin (2*k+d+3))) [DecidableRel H.Adj] (hcrit : is_k_factor_critical Hᶜ (2*k)) (x y u v : Fin (2*k+d+3)) (hxy : x ≠ y) (hxu : x ≠ u) (hyu : y ≠ u) (Q W : Finset (Fin (2*k+d+3))) (hqx : x ∉ Q) (hqy : y ∉ Q) (hwu : u ∉ W) (hq : Q.card + W.card = d + 1) (hw : Even W.card) (hw2 : 2 ≤ W.card) (hW : ∀ w ∈ W, H.Adj x w ∧ H.Adj y w ∧ (w ≠ v → H.Adj u w)) (hcross : ∀ q ∈ Q, ∀ w ∈ W, H.Adj q w) : u ∈ Q := by
  classical
  by_contra huq
  have hthree : W.card - 1 ≤ (W.erase v).card := by
    by_cases hv : v ∈ W
    · rw [Finset.card_erase_of_mem hv]
    · rw [Finset.erase_eq_of_notMem hv]; omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hthree
  let B := insert x (insert y (insert u Q))
  have hxnot : x ∉ insert y (insert u Q) := by simp [hxy, hxu, hqx]
  have hynot : y ∉ insert u Q := by simp [hyu, hqy]
  have hBcard : B.card = Q.card + 3 := by
    dsimp [B]
    rw [Finset.card_insert_of_notMem hxnot, Finset.card_insert_of_notMem hynot,
      Finset.card_insert_of_notMem huq]
  have hTW : T ⊆ W := fun a ha => Finset.mem_of_mem_erase (hTsub ha)
  have hTv : ∀ a ∈ T, a ≠ v := fun a ha => Finset.ne_of_mem_erase (hTsub ha)
  have hdisj : Disjoint T B := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have hax := (hW a (hTW ha)).1
    have hay := (hW a (hTW ha)).2.1
    have hau := (hW a (hTW ha)).2.2 (hTv a ha)
    dsimp [B] at hb
    simp only [Finset.mem_insert] at hb
    rcases hb with rfl | rfl | rfl | haq
    · exact H.irrefl hax
    · exact H.irrefl hay
    · exact H.irrefl hau
    · exact H.irrefl (hcross a haq a (hTW ha))
  have hcross' : ∀ a ∈ T, ∀ b ∈ B, ¬ Hᶜ.Adj a b := by
    intro a ha b hb hab
    have hax := (hW a (hTW ha)).1.symm
    have hay := (hW a (hTW ha)).2.1.symm
    have hau := ((hW a (hTW ha)).2.2 (hTv a ha)).symm
    have habH : H.Adj a b := by
      dsimp [B] at hb
      simp only [Finset.mem_insert] at hb
      rcases hb with rfl | rfl | rfl | hb
      · exact hax
      · exact hay
      · exact hau
      · exact (hcross b hb a (hTW ha)).symm
    exact hab.2 habH
  have hunion : (T ∪ B).card = d+3 := by
    rw [Finset.card_union_of_disjoint hdisj, hTcard, hBcard]
    omega
  have hcut : ((Finset.univ : Finset (Fin (2*k+d+3))) \ (T ∪ B)).card = 2*k := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (T ∪ B))
    simp only [Finset.card_univ, Fintype.card_fin, hunion] at h
    omega
  have heven := factor_critical_anticomplete_cut_side_even Hᶜ (2*k) hcrit T B hdisj hcross' hcut
  rw [hTcard] at heven
  rcases hw with ⟨a, ha⟩
  rcases heven with ⟨b, hb⟩
  omega
