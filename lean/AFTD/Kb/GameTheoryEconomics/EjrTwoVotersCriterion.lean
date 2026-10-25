import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEjrCommitteeIffCandidateSubsets
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.IsEjrCommittee

/-!
# ejr_two_voters_criterion

Topic: social_choice   Node: a10447fe4c72

Provenance: helper lemma. step towards ejr_chain_two_voters

For two voters, a committee W of size k satisfies EJR whenever: (1) if k ≤ |A 0 ∩ A 1| then W ⊆ A 0 ∩ A 1; (2) if |A 0 ∩ A 1| ≤ k then A 0 ∩ A 1 ⊆ W; and (3) for each voter i ∈ {0, 1}, if |A i ∩ W| < |A i| then k ≤ 2 * |A i ∩ W| + 1.
-/

/-- For two voters, a committee W of size k satisfies EJR whenever: (1) if k ≤ |A 0 ∩ A 1| then W ⊆ A 0 ∩ A 1; (2) if |A 0 ∩ A 1| ≤ k then A 0 ∩ A 1 ⊆ W; and (3) for each voter i ∈ {0, 1}, if |A i ∩ W| < |A i| then k ≤ 2 * |A i ∩ W| + 1. -/
theorem ejr_two_voters_criterion {m : ℕ} (A : Fin 2 → Finset (Fin m))
    (k : ℕ) (W : Finset (Fin m)) (hWcard : W.card = k)
    (hA : k ≤ (A 0 ∩ A 1).card → W ⊆ A 0 ∩ A 1)
    (hB : (A 0 ∩ A 1).card ≤ k → A 0 ∩ A 1 ⊆ W)
    (hD : (A 0 ∩ W).card < (A 0).card → k ≤ 2 * (A 0 ∩ W).card + 1)
    (hE : (A 1 ∩ W).card < (A 1).card → k ≤ 2 * (A 1 ∩ W).card + 1) :
    is_ejr_committee A k W := by
  rw [is_ejr_committee_iff_candidate_subsets]
  refine ⟨hWcard, fun T hT => ?_⟩
  have hTpos : 0 < T.card := Finset.Nonempty.card_pos hT
  generalize hS : (Finset.univ.filter fun i : Fin 2 => T ⊆ A i ∧ (A i ∩ W).card < T.card) = S
  have hS_le : S.card ≤ 2 := by
    rw [← hS]
    have := Finset.card_le_univ (Finset.univ.filter fun i : Fin 2 => T ⊆ A i ∧ (A i ∩ W).card < T.card)
    simpa using this
  interval_cases hSc : S.card
  · rw [zero_mul]
    exact mul_pos hTpos (by decide)
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hSc
    have hiS : i ∈ S := by rw [hi]; exact Finset.mem_singleton_self i
    rw [← hS, Finset.mem_filter] at hiS
    fin_cases i
    · dsimp at hiS
      obtain ⟨-, hsub, hlt⟩ := hiS
      have hTleA : T.card ≤ (A 0).card := Finset.card_le_card hsub
      have hltA : (A 0 ∩ W).card < (A 0).card := lt_of_lt_of_le hlt hTleA
      have hk := hD hltA
      linarith
    · dsimp at hiS
      obtain ⟨-, hsub, hlt⟩ := hiS
      have hTleA : T.card ≤ (A 1).card := Finset.card_le_card hsub
      have hltA : (A 1 ∩ W).card < (A 1).card := lt_of_lt_of_le hlt hTleA
      have hk := hE hltA
      linarith
  · have hS_univ : S = Finset.univ := Finset.eq_univ_of_card S (by simpa using hSc)
    have h0S : (0 : Fin 2) ∈ S := by rw [hS_univ]; exact Finset.mem_univ 0
    have h1S : (1 : Fin 2) ∈ S := by rw [hS_univ]; exact Finset.mem_univ 1
    rw [← hS, Finset.mem_filter] at h0S h1S
    obtain ⟨-, hT0, hlt0⟩ := h0S
    obtain ⟨-, hT1, hlt1⟩ := h1S
    have hTsub : T ⊆ A 0 ∩ A 1 := Finset.subset_inter hT0 hT1
    by_contra hnot
    have hTk : T.card ≤ k := by linarith
    rcases le_total ((A 0 ∩ A 1).card) k with hle | hle
    · have hsubW : A 0 ∩ A 1 ⊆ W := hB hle
      have hTW : T ⊆ W := Finset.Subset.trans hTsub hsubW
      have hT0W : T ⊆ A 0 ∩ W := Finset.subset_inter hT0 hTW
      have hle_card : T.card ≤ (A 0 ∩ W).card := Finset.card_le_card hT0W
      linarith
    · have hWsub : W ⊆ A 0 ∩ A 1 := hA hle
      have hW0 : W ⊆ A 0 := Finset.Subset.trans hWsub Finset.inter_subset_left
      have hAW : A 0 ∩ W = W := Finset.inter_eq_right.mpr hW0
      have hcard : (A 0 ∩ W).card = k := by rw [hAW, hWcard]
      linarith
