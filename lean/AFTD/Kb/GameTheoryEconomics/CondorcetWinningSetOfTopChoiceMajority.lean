import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet
import AFTD.Kb.GameTheoryEconomics.OutsideVotersSubsetTopChoicesCompl

/-!
# condorcet_winning_set_of_top_choice_majority

Topic: social_choice   Node: c5388eb4cd15

Provenance: helper lemma. step towards condorcet_dimension_le_three

Any candidate set S whose complement contains the top choice of strictly fewer than n/2 voters (i.e. S contains the top choices of a strict majority of voters) is a Condorcet winning set.
-/

/-- A candidate set containing the top choice of a strict majority of voters is a Condorcet winning set. -/
theorem condorcet_winning_set_of_top_choice_majority {n m : ℕ} (P : Fin n → Equiv.Perm (Fin m))
    (hm : 0 < m) (S : Finset (Fin m))
    (hS : 2 * (Finset.univ.filter fun v => (P v).symm ⟨0, hm⟩ ∉ S).card < n) :
    is_condorcet_winning_set P S := by
  intro a _ha
  have hsub := outside_voters_subset_top_choices_compl P S a hm
  have hcard := Finset.card_le_card hsub
  omega
