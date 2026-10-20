import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RoundRobinAlpha
import AFTD.Kb.GameTheoryEconomics.IsGuaranteedRoundRobinEf1Factor

/-!
# round_robin_alpha_three_eq_of_two_directions

Topic: fair_division   Node: aab058f25ecb

Provenance: helper lemma. step towards round_robin_alpha_three_eq_two_thirds

If 2/3 is a guaranteed EF1 factor for three agents and no factor above 2/3 is guaranteed, then the best guaranteed factor for three agents is 2/3.
-/

/-- Assembly step: the two halves of the characterisation give round_robin_alpha 3 = 2/3. -/
theorem round_robin_alpha_three_eq_of_two_directions
    (hlow : is_guaranteed_round_robin_ef1_factor 3 (2 / 3))
    (hup : ∀ α : ℝ, 2 / 3 < α → ¬ is_guaranteed_round_robin_ef1_factor 3 α) :
    round_robin_alpha 3 = 2 / 3 := by
  set s : Set ℝ := {α : ℝ | is_guaranteed_round_robin_ef1_factor 3 α} with hs
  have hne : s.Nonempty := ⟨2 / 3, hlow⟩
  have hupper : ∀ a ∈ s, a ≤ 2 / 3 := fun a ha => le_of_not_gt fun h => hup a h ha
  have hbdd : BddAbove s := ⟨2 / 3, hupper⟩
  have hmain : round_robin_alpha 3 = sSup s := rfl
  rw [hmain]
  exact le_antisymm (csSup_le hne hupper) (le_csSup hbdd hlow)
