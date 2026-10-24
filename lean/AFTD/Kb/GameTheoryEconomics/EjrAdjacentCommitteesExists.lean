import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EjrGreedyCohesivePairAux
import AFTD.Kb.GameTheoryEconomics.IsEjrCommittee
import AFTD.Kb.GameTheoryEconomics.IsEjrCohesiveGroup
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# ejr_adjacent_committees_exists

Topic: social_choice   Node: 7d01dd967f8e

Provenance: formalization of a published result. Source: arXiv:2302.01989, Robust and Verifiable Proportionality Axioms for Multiwinner Voting, Proposition 8: EJR consequence of the published EJR+ nested-pair theorem; this proof uses a strengthened greedy cohesive argument instead of the priceability proof.

For every approval profile with at least one voter and every k smaller than the candidate count, there exist nested committees W subset V satisfying EJR at sizes k and k+1, respectively.
-/

theorem ejr_adjacent_committees_exists {n m : ℕ}
    (A : Fin n → Finset (Fin m)) (hn : 0 < n) (k : ℕ) (hk : k < m) :
    ∃ W V : Finset (Fin m), W ⊆ V ∧ is_ejr_committee A k W ∧
      is_ejr_committee A (k + 1) V := by
  classical
  obtain ⟨W0, hbudget, hrep, hpair⟩ :=
    ejr_greedy_cohesive_pair_aux A (k + 1) hn (by omega) Finset.univ
  have hbudget' : W0.card * n ≤ n * (k + 1) := by simpa using hbudget
  have hW0 : W0.card ≤ k + 1 := by nlinarith
  by_cases hsmall : W0.card ≤ k
  · obtain ⟨W, hWsub, hWcard⟩ :=
      Finset.exists_superset_card_eq hsmall (show k ≤ Fintype.card (Fin m) by simpa using hk.le)
    obtain ⟨V, hVsub, hVcard⟩ := Finset.exists_superset_card_eq
      (show W.card ≤ k + 1 by omega)
      (show k + 1 ≤ Fintype.card (Fin m) by simpa using hk)
    refine ⟨W, V, hVsub, ⟨hWcard, ?_⟩, ⟨hVcard, ?_⟩⟩
    · intro ℓ hℓ G hG
      have hG' : is_ejr_cohesive_group A (k + 1) ℓ G :=
        ⟨hG.1.trans (Nat.mul_le_mul_left G.card (Nat.le_succ k)), hG.2⟩
      obtain ⟨i, hi, hu⟩ := hrep ℓ hℓ G (Finset.subset_univ _) hG'
      exact ⟨i, hi, hu.trans (Finset.card_le_card (Finset.inter_subset_inter_left hWsub))⟩
    · intro ℓ hℓ G hG
      obtain ⟨i, hi, hu⟩ := hrep ℓ hℓ G (Finset.subset_univ _) hG
      exact ⟨i, hi, hu.trans (Finset.card_le_card
        (Finset.inter_subset_inter_left (hWsub.trans hVsub)))⟩
  · have hWcard : W0.card = k + 1 := by omega
    have hfull : W0.card * n = (Finset.univ : Finset (Fin n)).card * (k + 1) := by
      simp [hWcard, Nat.mul_comm]
    have hne : W0.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨c, hc, hcpair⟩ := hpair hfull hne
    refine ⟨W0.erase c, W0, Finset.erase_subset _ _, ⟨?_, ?_⟩, ⟨hWcard, ?_⟩⟩
    · rw [Finset.card_erase_of_mem hc, hWcard]
      omega
    · intro ℓ hℓ G hG
      have := hcpair ℓ hℓ G (Finset.subset_univ _)
      simpa using this hG
    · intro ℓ hℓ G hG
      exact hrep ℓ hℓ G (Finset.subset_univ _) hG
