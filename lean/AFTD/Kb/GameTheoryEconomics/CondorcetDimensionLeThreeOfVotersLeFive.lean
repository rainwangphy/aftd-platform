import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetWinningSetOfTopChoices
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet

/-!
# condorcet_dimension_le_three_of_voters_le_five

Topic: social_choice   Node: 83ef8d853778

Provenance: helper lemma. step towards condorcet_dimension_le_three

Every election with at most 5 voters (and at least 1 voter) has a Condorcet winning set of at most 3 candidates: selecting the top-choice candidate of each of the first min(n, 3) voters yields a winning set of size at most 3.
-/

/-- Every election with at most 5 voters and at least 1 voter has a Condorcet winning set of at most 3 candidates. -/
theorem condorcet_dimension_le_three_of_voters_le_five (n m : ℕ) (P : Fin n → Equiv.Perm (Fin m))
    (hn : 0 < n) (hn5 : n ≤ 5) :
    ∃ S : Finset (Fin m), S.card ≤ 3 ∧ is_condorcet_winning_set P S := by
  by_cases hm : m = 0
  · subst hm
    exact ⟨∅, by simp, by simp [is_condorcet_winning_set]⟩
  · have hm' : 0 < m := Nat.pos_of_ne_zero hm
    refine ⟨(Finset.univ.filter (fun v : Fin n => (v:ℕ) < 3)).image (fun v => (P v).symm ⟨0, hm'⟩), ?_, ?_⟩
    · calc _ ≤ (Finset.univ.filter (fun v : Fin n => (v:ℕ) < 3)).card := Finset.card_image_le
        _ ≤ 3 := by interval_cases n <;> decide
    · refine condorcet_winning_set_of_top_choices P hm' _ ?_
      interval_cases n <;> decide
