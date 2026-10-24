import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEjrCohesiveGroup
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# ejr_greedy_cohesive_pair_aux

Topic: social_choice   Node: b023c47b67ca

Provenance: helper lemma. Helper for ejr_adjacent_committees_exists (arXiv:2302.01989, Proposition 8, EJR consequence): strengthen the existing greedy cohesive budget argument with a deletion certificate when the budget is exactly saturated.

For every voter subset S and positive committee parameter K, a greedy cohesive core W has cost at most |S|K/n and satisfies every K-cohesive group in S; if its budget is saturated and W is nonempty, one candidate can be erased while satisfying every (K-1)-cohesive group in S.
-/

theorem ejr_greedy_cohesive_pair_aux {n m : ℕ}
    (A : Fin n → Finset (Fin m)) (K : ℕ) (hn : 0 < n) (hK : 0 < K)
    (S : Finset (Fin n)) :
    ∃ W : Finset (Fin m), W.card * n ≤ S.card * K ∧
      (∀ ℓ, 1 ≤ ℓ → ∀ G ⊆ S, is_ejr_cohesive_group A K ℓ G →
        ∃ i ∈ G, ℓ ≤ (A i ∩ W).card) ∧
      (W.card * n = S.card * K → W.Nonempty → ∃ c ∈ W,
        ∀ ℓ, 1 ≤ ℓ → ∀ G ⊆ S, is_ejr_cohesive_group A (K - 1) ℓ G →
          ∃ i ∈ G, ℓ ≤ (A i ∩ W.erase c).card) := by
  classical
  induction S using Finset.strongInduction with
  | H S ih =>
    have hle_m : ∀ ℓ G, is_ejr_cohesive_group A K ℓ G → ℓ ≤ m := fun ℓ G h =>
      h.2.trans ((Finset.card_le_univ _).trans (by simp))
    have upgrade : ∀ ℓ G, is_ejr_cohesive_group A (K - 1) ℓ G →
        is_ejr_cohesive_group A K ℓ G := by
      intro ℓ G h
      exact ⟨h.1.trans (Nat.mul_le_mul_left G.card (Nat.sub_le K 1)), h.2⟩
    let P : Finset (ℕ × Finset (Fin n)) :=
      ((Finset.Icc 1 m) ×ˢ S.powerset).filter fun p => is_ejr_cohesive_group A K p.1 p.2
    have hmemP : ∀ ℓ G, (ℓ, G) ∈ P ↔
        (1 ≤ ℓ ∧ G ⊆ S ∧ is_ejr_cohesive_group A K ℓ G) := by
      intro ℓ G
      simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_powerset]
      constructor
      · rintro ⟨⟨⟨h1, -⟩, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨⟨h1, hle_m ℓ G h3⟩, h2⟩, h3⟩
    by_cases hP : P.Nonempty
    · obtain ⟨⟨ℓ, G⟩, hpP, hmax⟩ := P.exists_max_image Prod.fst hP
      obtain ⟨hℓ1, hGS, hcoh⟩ := (hmemP ℓ G).1 hpP
      have hGne : G.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        have h := hcoh.1
        simp only [Finset.card_empty, zero_mul] at h
        have : 0 < ℓ * n := Nat.mul_pos hℓ1 hn
        omega
      obtain ⟨W', hW'card, hW', hW'pair⟩ :=
        ih (S \ G) (Finset.sdiff_ssubset hGS hGne)
      obtain ⟨C, hCsub, hCcard⟩ := Finset.exists_subset_card_eq hcoh.2
      have hsum : (S \ G).card + G.card = S.card :=
        Finset.card_sdiff_add_card_eq_card hGS
      have hbudget : (W' ∪ C).card * n ≤ S.card * K := by
        have h1 : (W' ∪ C).card ≤ W'.card + ℓ :=
          (Finset.card_union_le _ _).trans (by rw [hCcard])
        calc (W' ∪ C).card * n ≤ (W'.card + ℓ) * n := Nat.mul_le_mul_right _ h1
          _ = W'.card * n + ℓ * n := by ring
          _ ≤ (S \ G).card * K + G.card * K := Nat.add_le_add hW'card hcoh.1
          _ = S.card * K := by rw [← Nat.add_mul, hsum]
      refine ⟨W' ∪ C, hbudget, ?_, ?_⟩
      · intro ℓ' hℓ' H hHS hHcoh
        by_cases hHG : Disjoint H G
        · have hHsub : H ⊆ S \ G := fun x hx =>
            Finset.mem_sdiff.2 ⟨hHS hx, Finset.disjoint_left.1 hHG hx⟩
          obtain ⟨i, hi, hle⟩ := hW' ℓ' hℓ' H hHsub hHcoh
          exact ⟨i, hi, hle.trans (Finset.card_le_card
            (Finset.inter_subset_inter_left Finset.subset_union_left))⟩
        · obtain ⟨i, hiH, hiG⟩ := Finset.not_disjoint_iff.1 hHG
          have hℓ'le : ℓ' ≤ ℓ := hmax (ℓ', H) ((hmemP ℓ' H).2 ⟨hℓ', hHS, hHcoh⟩)
          refine ⟨i, hiH, hℓ'le.trans ?_⟩
          rw [← hCcard]
          apply Finset.card_le_card
          intro c hc
          exact Finset.mem_inter.2 ⟨(Finset.mem_filter.1 (hCsub hc)).2 i hiG,
            Finset.mem_union_right _ hc⟩
      · intro hfull hne
        have hcardU : (W' ∪ C).card ≤ W'.card + ℓ :=
          (Finset.card_union_le _ _).trans (by rw [hCcard])
        have hmulU := Nat.mul_le_mul_right n hcardU
        have hsumK : (S \ G).card * K + G.card * K = S.card * K := by
          rw [← Nat.add_mul, hsum]
        have hW'full : W'.card * n = (S \ G).card * K := by nlinarith [hcoh.1]
        have hGfull : ℓ * n = G.card * K := by nlinarith [hcoh.1]
        have hcardEq : (W' ∪ C).card = W'.card + C.card := by
          rw [hCcard]
          have heq : (W' ∪ C).card * n = (W'.card + ℓ) * n := by nlinarith
          nlinarith
        have hdisj : Disjoint W' C := Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp (by
          have := Finset.card_union_add_card_inter W' C
          omega))
        by_cases hW'ne : W'.Nonempty
        · obtain ⟨c, hc, hcpair⟩ := hW'pair hW'full hW'ne
          refine ⟨c, Finset.mem_union_left _ hc, ?_⟩
          have hcC : c ∉ C := Finset.disjoint_left.mp hdisj hc
          intro ℓ' hℓ' H hHS hHcoh
          by_cases hHG : Disjoint H G
          · have hHsub : H ⊆ S \ G := fun x hx =>
              Finset.mem_sdiff.2 ⟨hHS hx, Finset.disjoint_left.1 hHG hx⟩
            obtain ⟨i, hi, hle⟩ := hcpair ℓ' hℓ' H hHsub hHcoh
            exact ⟨i, hi, hle.trans (Finset.card_le_card
              (Finset.inter_subset_inter_left
                (Finset.erase_subset_erase c Finset.subset_union_left)))⟩
          · obtain ⟨i, hiH, hiG⟩ := Finset.not_disjoint_iff.1 hHG
            have hℓ'le : ℓ' ≤ ℓ :=
              hmax (ℓ', H) ((hmemP ℓ' H).2 ⟨hℓ', hHS, upgrade ℓ' H hHcoh⟩)
            refine ⟨i, hiH, hℓ'le.trans ?_⟩
            rw [← hCcard]
            apply Finset.card_le_card
            intro d hd
            refine Finset.mem_inter.2 ⟨(Finset.mem_filter.1 (hCsub hd)).2 i hiG, ?_⟩
            exact Finset.mem_erase.mpr ⟨fun he => hcC (he ▸ hd), Finset.mem_union_right _ hd⟩
        · have hW'empty : W' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW'ne
          have hrem0 : (S \ G).card = 0 := by
            have hzero : (S \ G).card * K = 0 := by simpa [hW'empty] using hW'full.symm
            rcases Nat.mul_eq_zero.mp hzero with h | h
            · exact h
            · omega
          have hSG : S ⊆ G := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hrem0)
          have hCne : C.Nonempty := Finset.card_pos.mp (by omega)
          obtain ⟨c, hc⟩ := hCne
          refine ⟨c, Finset.mem_union_right _ hc, ?_⟩
          intro ℓ' hℓ' H hHS hHcoh
          have hℓ'le : ℓ' ≤ ℓ :=
            hmax (ℓ', H) ((hmemP ℓ' H).2 ⟨hℓ', hHS, upgrade ℓ' H hHcoh⟩)
          have hHcard : H.card ≤ G.card := Finset.card_le_card (hHS.trans hSG)
          have hGpos : 0 < G.card := Finset.card_pos.mpr hGne
          have hmulH := Nat.mul_le_mul_right (K - 1) hHcard
          have hstrict : G.card * (K - 1) < G.card * K :=
            Nat.mul_lt_mul_of_pos_left (by omega) hGpos
          have hℓ'lt : ℓ' < ℓ := by
            by_contra hnot
            have heq : ℓ' = ℓ := by omega
            have hsize := hHcoh.1
            rw [heq] at hsize
            omega
          have hHne : H.Nonempty := by
            rw [← Finset.card_pos]
            have hsize := hHcoh.1
            have hpos : 0 < ℓ' * n := Nat.mul_pos hℓ' hn
            nlinarith
          obtain ⟨i, hi⟩ := hHne
          refine ⟨i, hi, ?_⟩
          have hCerase : (C.erase c).card = ℓ - 1 := by
            rw [Finset.card_erase_of_mem hc, hCcard]
          have hsub : C.erase c ⊆ A i ∩ (W' ∪ C).erase c := by
            intro d hd
            obtain ⟨hdc, hdC⟩ := Finset.mem_erase.mp hd
            exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp (hCsub hdC)).2 i (hSG (hHS hi)),
              Finset.mem_erase.mpr ⟨hdc, Finset.mem_union_right _ hdC⟩⟩
          have := Finset.card_le_card hsub
          omega
    · refine ⟨∅, by simp, ?_, ?_⟩
      · intro ℓ hℓ G hGS hcoh
        exact absurd ⟨(ℓ, G), (hmemP ℓ G).2 ⟨hℓ, hGS, hcoh⟩⟩ hP
      · intro _ hne
        simp at hne
