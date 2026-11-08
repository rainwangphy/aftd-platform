import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ChoreResidualCost
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# chore_residual_cost_of_card_le

Topic: fair_division   Node: 00b1df92b850

Provenance: formalization of a published result. Source: arXiv:2611.07468 Def. 2.1

Given a type α with decidable equality, a cost function c : α → NNReal, a natural number k : ℕ, and a bundle S : Finset α with S.card ≤ k, the k-chore residual cost chore_residual_cost c k S is 0.
-/

/-- If a bundle S contains at most k chores, its k-chore residual cost is 0. -/
theorem chore_residual_cost_of_card_le {α : Type*} [DecidableEq α]
    (c : α → NNReal) (k : ℕ) (S : Finset α) (h : S.card ≤ k) :
    chore_residual_cost c k S = 0 := by
  unfold chore_residual_cost
  have hone : ∀ T : {T : Finset α // T ⊆ S ∧ T.card = min k S.card},
      ∑ x ∈ S \ T.val, c x = 0 := by
    intro T
    have hcard : T.val.card = S.card := by
      rw [T.2.2, Nat.min_eq_right h]
    have hTS : T.val = S := Finset.eq_of_subset_of_card_le T.2.1 (le_of_eq hcard.symm)
    simp [hTS]
  refine le_antisymm (ciSup_le' ?_) zero_le
  intro T
  rw [hone T]
