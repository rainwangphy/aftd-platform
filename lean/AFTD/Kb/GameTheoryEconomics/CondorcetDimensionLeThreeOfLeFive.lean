import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetWinningSetOfTopChoiceMajority
import AFTD.Kb.GameTheoryEconomics.CondorcetDimensionLeThreeOfLeFour
import AFTD.Kb.GameTheoryEconomics.CondorcetBalancedTopImpliesSixLeCandidates
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet

/-!
# condorcet_dimension_le_three_of_le_five

Topic: social_choice   Node: 33165b9af0cc

Provenance: helper lemma. step towards condorcet_dimension_le_three

Every election with at most 5 candidates (and at least 1 voter) has a Condorcet winning set of at most 3 candidates.
-/

/-- Every election with at most five candidates has a Condorcet winning set of size at most three. -/
theorem condorcet_dimension_le_three_of_le_five (n m : ℕ) (P : Fin n → Equiv.Perm (Fin m))
    (hn : 0 < n) (hm : m ≤ 5) :
    ∃ S : Finset (Fin m), S.card ≤ 3 ∧ is_condorcet_winning_set P S := by
  by_cases hm4 : m ≤ 4
  · exact condorcet_dimension_le_three_of_le_four n m P hn hm4
  have hm_ge4 : 4 ≤ m := by omega
  have hm_pos : 0 < m := by omega
  have hbal : ¬ (∀ S : Finset (Fin m), S.card = 3 →
      2 * (Finset.univ.filter fun v => (P v).symm ⟨0, by omega⟩ ∈ S).card ≤ n) := by
    intro h
    have h6 := condorcet_balanced_top_implies_six_le_candidates n m P hn hm_ge4 h
    omega
  push Not at hbal
  obtain ⟨S, hScard, hSgt⟩ := hbal
  have hpart := Finset.card_filter_add_card_filter_not
    (fun v => (P v).symm ⟨0, hm_pos⟩ ∈ S) (s := (Finset.univ : Finset (Fin n)))
  simp only [Finset.card_univ, Fintype.card_fin] at hpart
  have h_not : 2 * (Finset.univ.filter fun v => (P v).symm ⟨0, hm_pos⟩ ∉ S).card < n := by
    omega
  refine ⟨S, by omega, ?_⟩
  exact condorcet_winning_set_of_top_choice_majority P hm_pos S h_not
