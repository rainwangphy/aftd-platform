import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ChoreResidualCost
import AFTD.Kb.GameTheoryEconomics.BlockInsertionResidualCostBoundOfLe
import AFTD.Kb.GameTheoryEconomics.BlockInsertionResidualCostBoundOfGt
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# block_insertion_residual_cost_bound

Topic: fair_division   Node: eaddc2866d9b

Provenance: formalization of a published result. Source: arXiv:2611.07468 Lemma B.1

Given a type α with decidable equality, a cost function c : α → NNReal, a natural number k : ℕ with 1 ≤ k, a bundle B : Finset α with k ≤ B.card, and a bundle E : Finset α of r chores disjoint from B with E.card = r such that c e ≤ c b for all e ∈ E and b ∈ B, the k-chore residual cost chore_residual_cost c k (B ∪ E) is at most max 1 ((r : NNReal) / (k : NNReal)) * ∑ b ∈ B, c b.
-/

/-- Block insertion cost bound for EFkX residuals (Lemma B.1). -/
theorem block_insertion_residual_cost_bound {α : Type*} [DecidableEq α]
    (c : α → NNReal) (k : ℕ) (hk : 1 ≤ k)
    (B E : Finset α) (r : ℕ) (hr : E.card = r)
    (hdisj : Disjoint B E) (hkB : k ≤ B.card)
    (h_cost : ∀ e ∈ E, ∀ b ∈ B, c e ≤ c b) :
    chore_residual_cost c k (B ∪ E) ≤
      max 1 ((r : NNReal) / (k : NNReal)) * ∑ b ∈ B, c b := by
  by_cases hrk : r ≤ k
  · have hrk' : E.card ≤ k := hr.symm ▸ hrk
    have hle := block_insertion_residual_cost_bound_of_le c k B E hdisj hkB hrk' h_cost
    have hmax : (1 : NNReal) ≤ max 1 ((r : NNReal) / (k : NNReal)) := le_max_left 1 _
    have h1 : ∑ b ∈ B, c b ≤ max 1 ((r : NNReal) / (k : NNReal)) * ∑ b ∈ B, c b := by
      conv_lhs => rw [← one_mul (∑ b ∈ B, c b)]
      gcongr
    exact hle.trans h1
  · have hrk' : k < E.card := by
      rw [hr]
      omega
    have hgt := block_insertion_residual_cost_bound_of_gt c k hk B E hdisj hkB hrk' h_cost
    have hmax : ((r : NNReal) / (k : NNReal)) ≤ max 1 ((r : NNReal) / (k : NNReal)) := le_max_right _ _
    rw [hr] at hgt
    have h2 : ((r : NNReal) / (k : NNReal)) * ∑ b ∈ B, c b ≤
        max 1 ((r : NNReal) / (k : NNReal)) * ∑ b ∈ B, c b := by
      gcongr
    exact hgt.trans h2
