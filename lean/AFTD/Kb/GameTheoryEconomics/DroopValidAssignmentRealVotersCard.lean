import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsDroopValidAssignment

/-!
# droop_valid_assignment_real_voters_card

Topic: social_choice   Node: be11a4b1c0a8

Provenance: helper lemma. arXiv:2508.00811, Def. 16

For any Droop-valid Monroe assignment π of n voters to committee size k, the number of voters assigned to a real candidate (not none) is exactly n - n / (k + 1).
-/

/-- In any Droop-valid Monroe assignment, the number of voters assigned to real candidates is n - ⌊n/(k+1)⌋. -/
theorem droop_valid_assignment_real_voters_card {n m k : ℕ} {W : Finset (Fin m)}
    {π : Fin n → Option (Fin m)} (hv : is_droop_valid_assignment k W π) :
    (Finset.univ.filter fun i => π i ≠ none).card = n - n / (k + 1) := by
  have hdummy : (Finset.univ.filter fun i => π i = none).card = n / (k + 1) := hv.2.2.2
  have h_compl : (Finset.univ.filter fun i => π i ≠ none) = Finset.univ \ (Finset.univ.filter fun i => π i = none) := by
    ext i
    simp
  rw [h_compl, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
  simp [hdummy]
