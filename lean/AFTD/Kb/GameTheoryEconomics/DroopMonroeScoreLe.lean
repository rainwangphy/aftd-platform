import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsDroopValidAssignment
import AFTD.Kb.GameTheoryEconomics.DroopMonroeScore

/-!
# droop_monroe_score_le

Topic: social_choice   Node: 6caaf1810cb7

A Droop-valid assignment scores at most n - ⌊n/(k+1)⌋, since the dummy voters are unsatisfied.
-/

/-- A Droop-valid assignment never scores more than `n - ⌊n/(k+1)⌋`: the dummy's voters are unsatisfied. -/
theorem droop_monroe_score_le {n m : ℕ} (A : Fin n → Finset (Fin m)) (k : ℕ) (W : Finset (Fin m))
    (π : Fin n → Option (Fin m)) (hv : is_droop_valid_assignment k W π) :
    droop_monroe_score A π + n / (k + 1) ≤ n := by
  have hsub : (Finset.univ.filter fun i => ∃ c, π i = some c ∧ c ∈ A i) ⊆
      Finset.univ.filter fun i => ¬ π i = none := by
    intro i hi
    obtain ⟨c, hc, _⟩ := (Finset.mem_filter.1 hi).2
    simp [hc]
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (p := fun i => π i = none)
  rw [hv.2.2.2] at h2
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  unfold droop_monroe_score
  omega
