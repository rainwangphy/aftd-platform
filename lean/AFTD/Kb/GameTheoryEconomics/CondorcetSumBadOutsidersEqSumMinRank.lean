import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetVoterBadOutsidersEqMinRank

/-!
# condorcet_sum_bad_outsiders_eq_sum_min_rank

Topic: social_choice   Node: 9b114deaed38

Provenance: helper lemma. step towards condorcet_dimension_le_three_balanced

Summing the number of voters who rank an outsider candidate above all of S across all outsiders equals the sum across voters of the minimum rank of S.
-/

/-- The total number of bad voters across all outside candidates equals the sum of the minimum ranks of S over all voters. -/
theorem condorcet_sum_bad_outsiders_eq_sum_min_rank {n m : ℕ} (P : Fin n → Equiv.Perm (Fin m))
    (S : Finset (Fin m)) (hS : S.Nonempty) :
    (∑ a ∈ Finset.univ \ S, (Finset.univ.filter (fun v => ∀ s ∈ S, P v a < P v s)).card) =
      ∑ v : Fin n, (S.image (fun s => (P v s).val)).min' (hS.image _) := by
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  simp_rw [← Finset.card_filter, condorcet_voter_bad_outsiders_eq_min_rank _ S hS]
