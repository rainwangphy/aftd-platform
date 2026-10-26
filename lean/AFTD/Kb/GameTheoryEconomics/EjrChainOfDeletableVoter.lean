import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEjrCommitteeIffCandidateSubsets
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.IsEjrCommittee

/-!
# ejr_chain_of_deletable_voter

Topic: social_choice   Node: 66e450b9312e

Provenance: helper lemma. step towards ejr_committee_monotone_chain_exists

If a voter's ballot is empty or misses at most one candidate, deleting that voter preserves the existence of an EJR chain: the same ordering witnesses the chain for the original profile.
-/

theorem ejr_chain_of_deletable_voter_card_filter_split {n : ℕ} (i : Fin n)
    (e : Fin (n - 1) ≃ {j : Fin n // j ≠ i})
    (P : Fin n → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = (if P i then 1 else 0) + (Finset.univ.filter (fun j => P (e j).1)).card := by
  have h1 : (Finset.univ.filter P).card = (if P i then 1 else 0) + (Finset.univ.filter (fun j => j ≠ i ∧ P j)).card := by
    by_cases hi : P i
    · rw [if_pos hi]
      have h_eq : Finset.univ.filter P = insert i (Finset.univ.filter (fun j => j ≠ i ∧ P j)) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        by_cases hx : x = i
        · subst hx; simp [hi]
        · simp [hx]
      rw [h_eq, Finset.card_insert_of_notMem]
      · omega
      · simp
    · rw [if_neg hi, zero_add]
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hx
        refine ⟨?_, hx⟩
        rintro rfl
        exact hi hx
      · intro hx
        exact hx.2
  have h2 : (Finset.univ.filter (fun j => j ≠ i ∧ P j)).card =
      ((Finset.univ : Finset {j : Fin n // j ≠ i}).filter (fun j => P j.1)).card := by
    have h := (Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩
      (s := (Finset.univ : Finset {j : Fin n // j ≠ i}).filter (fun j => P j.1))).symm
    rw [h]
    congr 1
    ext x
    simp
    tauto
  have h3 : (Finset.univ.filter (fun j => P (e j).1)).card =
      ((Finset.univ : Finset {j : Fin n // j ≠ i}).filter (fun j => P j.1)).card := by
    have : (Finset.univ.filter (fun j => P (e j).1)) =
        ((Finset.univ : Finset {j : Fin n // j ≠ i}).filter (fun j => P j.1)).map e.symm.toEmbedding := by
      ext a
      simp
    rw [this, Finset.card_map]
  rw [h1, h2, h3]

/-- Profile reduction deleting a voter with empty or nearly-full ballot, decreasing n with m fixed; the same permutation works. -/
theorem ejr_chain_of_deletable_voter (n m : ℕ) (A : Fin n → Finset (Fin m)) (hn : 0 < n)
    (i : Fin n) (hi : A i = ∅ ∨ m - 1 ≤ (A i).card)
    (B : Fin (n - 1) → Finset (Fin m)) (e : Fin (n - 1) ≃ {j : Fin n // j ≠ i})
    (hB : ∀ j, B j = A (e j).1)
    (hchain : ∃ σ' : Equiv.Perm (Fin m), ∀ k, k ≤ m →
      is_ejr_committee B k (Finset.univ.filter fun x => (σ' x : ℕ) < k)) :
    ∃ σ : Equiv.Perm (Fin m), ∀ k, k ≤ m →
      is_ejr_committee A k (Finset.univ.filter fun x => (σ x : ℕ) < k) := by
  rcases hchain with ⟨σ, hσ⟩
  use σ
  intro k hk
  have hB_ejr := hσ k hk
  rw [is_ejr_committee_iff_candidate_subsets] at hB_ejr ⊢
  rcases hB_ejr with ⟨hWcard, hB_subsets⟩
  refine ⟨hWcard, ?_⟩
  intro T hT
  set W := Finset.univ.filter fun x : Fin m => (σ x : ℕ) < k
  have hB_bound := hB_subsets T hT
  have h_split := ejr_chain_of_deletable_voter_card_filter_split (n := n) i e
    (fun j => T ⊆ A j ∧ (A j ∩ W).card < T.card)
  have h_congr : (Finset.univ.filter (fun j => T ⊆ A (e j).1 ∧ (A (e j).1 ∩ W).card < T.card)).card =
      (Finset.univ.filter (fun j => T ⊆ B j ∧ (B j ∩ W).card < T.card)).card := by
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hB j]
  rw [h_congr] at h_split
  set c_A := (Finset.univ.filter (fun j => T ⊆ A j ∧ (A j ∩ W).card < T.card)).card
  set c_B := (Finset.univ.filter (fun j => T ⊆ B j ∧ (B j ∩ W).card < T.card)).card
  have h_step : T.card * n = T.card * (n - 1) + T.card := by
    have : n = n - 1 + 1 := (Nat.sub_add_cancel (Nat.succ_le_of_lt hn)).symm
    conv_lhs => rw [this]
    ring
  by_cases hPi : T ⊆ A i ∧ (A i ∩ W).card < T.card
  · rw [if_pos hPi] at h_split
    have hcA : c_A = 1 + c_B := h_split
    have hAi_nonempty : A i ≠ ∅ := by
      intro hAi_empty
      have hTempty : T ⊆ ∅ := by
        have h := hPi.1
        rwa [hAi_empty] at h
      have : T = ∅ := Finset.subset_empty.mp hTempty
      exact Finset.nonempty_iff_ne_empty.mp hT this
    have hAi_card : m - 1 ≤ (A i).card := by
      cases hi with
      | inl h_empty => exact False.elim (hAi_nonempty h_empty)
      | inr h_ge => exact h_ge
    have h_union : (A i ∪ W).card ≤ m := by
      exact le_trans (Finset.card_le_univ (A i ∪ W)) (by simp)
    have h_inc_exc : (A i ∩ W).card + (A i ∪ W).card = (A i).card + W.card :=
      Finset.card_inter_add_card_union (A i) W
    have h_inter : k - 1 ≤ (A i ∩ W).card := by
      omega
    have h_k_le_T : k ≤ T.card := by
      omega
    rw [hcA, h_step]
    linarith
  · rw [if_neg hPi, zero_add] at h_split
    have hcA : c_A = c_B := h_split
    have hTpos : 0 < T.card := Finset.Nonempty.card_pos hT
    rw [hcA, h_step]
    linarith
