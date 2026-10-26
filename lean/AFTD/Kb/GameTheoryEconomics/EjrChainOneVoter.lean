import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEjrCommittee
import AFTD.Kb.GameTheoryEconomics.ExistsPermWithPrefixEqTake
import AFTD.Kb.GameTheoryEconomics.IsEjrCohesiveGroup

/-!
# ejr_chain_one_voter

Topic: social_choice   Node: f30e7b39fc4d

Provenance: helper lemma. step towards ejr_committee_monotone_chain_exists

Every approval profile with exactly one voter admits an EJR committee chain.
-/

/-- Every approval profile with exactly one voter admits an EJR committee chain. -/
theorem ejr_chain_one_voter {m : ℕ} (A : Fin 1 → Finset (Fin m)) :
    ∃ σ : Equiv.Perm (Fin m), ∀ k, k ≤ m →
      is_ejr_committee A k (Finset.univ.filter fun c => (σ c : ℕ) < k) := by
  let A0 := A 0
  let B := Finset.univ \ A0
  let L := A0.toList ++ B.toList
  have hdisj : (A0.toList).Disjoint (B.toList) := by
    rw [List.disjoint_left]
    intro a ha hb
    have ha' : a ∈ A0 := Finset.mem_toList.mp ha
    have hb' : a ∈ B := Finset.mem_toList.mp hb
    simp only [B, Finset.mem_sdiff, Finset.mem_univ, true_and] at hb'
    exact hb' ha'
  have hLnodup : L.Nodup := List.Nodup.append A0.nodup_toList B.nodup_toList hdisj
  have hcardB : Finset.card B + Finset.card A0 = m := by
    have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A0)
    simpa [B, Finset.card_univ, Fintype.card_fin] using this
  have hLlen : L.length = m := by
    simp only [L, List.length_append, Finset.length_toList]
    omega
  obtain ⟨σ, hσ⟩ := exists_perm_with_prefix_eq_take L hLnodup hLlen
  refine ⟨σ, ?_⟩
  intro k hk
  have hW : Finset.univ.filter (fun c => (σ c : ℕ) < k) = (L.take k).toFinset := hσ k hk
  rw [hW]
  constructor
  · have htake_nodup : (L.take k).Nodup := (List.take_sublist k L).nodup hLnodup
    have htake_len : (L.take k).length = k := by
      rw [List.length_take, hLlen, min_eq_left hk]
    rw [List.toFinset_card_of_nodup htake_nodup, htake_len]
  · intro ℓ hℓ G hGcoh
    obtain ⟨hGcard, hcomm⟩ := hGcoh
    have hGne : G.Nonempty := by
      rcases Finset.eq_empty_or_nonempty G with h | h
      · exfalso
        rw [h] at hGcard
        simp only [Finset.card_empty] at hGcard
        omega
      · exact h
    have hGcard_le : Finset.card G ≤ 1 := by
      have := Finset.card_le_card (Finset.subset_univ G)
      simpa [Finset.card_univ] using this
    have hGpos : 0 < Finset.card G := Finset.card_pos.mpr hGne
    have hGc1 : Finset.card G = 1 := by omega
    have hℓk : ℓ ≤ k := by
      have := hGcard
      rw [hGc1] at this
      omega
    obtain ⟨i, hi⟩ := hGne
    have hi0 : i = 0 := Subsingleton.elim i 0
    have h0mem : (0 : Fin 1) ∈ G := hi0 ▸ hi
    have hsub : (({c | ∀ i ∈ G, c ∈ A i}) : Finset (Fin m)) ⊆ A0 := by
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      exact hc 0 h0mem
    have hA0ge : ℓ ≤ Finset.card A0 := le_trans hcomm (Finset.card_le_card hsub)
    refine ⟨0, h0mem, ?_⟩
    let S := (A0.toList.take k).toFinset
    have hSsub : S ⊆ A0 ∩ (L.take k).toFinset := by
      intro c hc
      rw [Finset.mem_inter]
      constructor
      · exact Finset.mem_toList.mp (List.mem_of_mem_take (List.mem_toFinset.mp hc))
      · rw [List.mem_toFinset]
        rw [List.take_append]
        exact List.mem_append_left _ (List.mem_toFinset.mp hc)
    have hScard : Finset.card S = min k (Finset.card A0) := by
      have hnd : (A0.toList.take k).Nodup := (List.take_sublist k A0.toList).nodup A0.nodup_toList
      rw [List.toFinset_card_of_nodup hnd, List.length_take, Finset.length_toList]
    have hmin : ℓ ≤ Finset.card S := by
      rw [hScard]
      exact le_min hℓk hA0ge
    exact le_trans hmin (Finset.card_le_card hSsub)
