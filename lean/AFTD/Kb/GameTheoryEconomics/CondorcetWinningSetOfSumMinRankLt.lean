import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetSumBadOutsidersEqSumMinRank
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet

/-!
# condorcet_winning_set_of_sum_min_rank_lt

Topic: social_choice   Node: 532f0fb6a224

Provenance: helper lemma. step towards condorcet_dimension_le_three_balanced

If 2 * (sum of min ranks of S) < n, then S is a Condorcet winning set.
-/

/-- If the sum of minimum ranks of S across all voters is strictly less than n/2, then S is a Condorcet winning set. -/
theorem condorcet_winning_set_of_sum_min_rank_lt {n m : ℕ} (P : Fin n → Equiv.Perm (Fin m))
    (S : Finset (Fin m)) (hS : S.Nonempty)
    (h_sum : 2 * (∑ v : Fin n, (S.image (fun s => (P v s).val)).min' (hS.image _)) < n) :
    is_condorcet_winning_set P S := by
  intro a ha
  have ha' : a ∈ Finset.univ \ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩
  have h_le := @Finset.single_le_sum (Fin m) ℕ _ _
    (fun x => (Finset.univ.filter (fun v => ∀ s ∈ S, P v x < P v s)).card)
    (Finset.univ \ S) _ (fun _ _ => Nat.zero_le _) a ha'
  have h_sum_eq := condorcet_sum_bad_outsiders_eq_sum_min_rank P S hS
  omega
