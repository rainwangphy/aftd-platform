import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsIdenticallyOrdered
import AFTD.Kb.GameTheoryEconomics.ChoreOppositePair
import AFTD.Kb.GameTheoryEconomics.ChoreRemainingSet
import AFTD.Kb.GameTheoryEconomics.IdoRemainingChoresCostLeOneThird
import AFTD.Kb.GameTheoryEconomics.IdoOppositePairCostLeFourThirds
import AFTD.Kb.GameTheoryEconomics.ChoreMaximinShare
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# ido_chore_opposite_pairs_cost_bounds

Topic: fair_division   Node: 0e65cb842a29

Provenance: formalization of a published result. Source: arXiv:2611.04884 Lemma 4.1

In an identically ordered instance of m chores and n agents with 2 * n ≤ m and nonnegative costs c where every agent has maximin share 1, for every agent i : Fin n, every chore g in chore_remaining_set m n has cost c i g ≤ 1/3, and for every index j : Fin n, the additive valuation of chore_opposite_pair h2n j under c i is at most 4/3.
-/

/-- Cost bounds for opposite pairs and remaining chores in an IDO instance with MMS 1. -/
theorem ido_chore_opposite_pairs_cost_bounds
    (n m : ℕ) (h2n : 2 * n ≤ m) (c : Fin n → Fin m → ℝ)
    (hc_nonneg : ∀ i e, 0 ≤ c i e)
    (h_ido : is_identically_ordered c)
    (h_mms : ∀ i : Fin n, chore_maximin_share n (c i) = 1) :
    (∀ (i : Fin n) (g : Fin m), g ∈ chore_remaining_set m n → c i g ≤ 1 / 3) ∧
    (∀ (i : Fin n) (j : Fin n), additive_valuation (c i) (chore_opposite_pair h2n j) ≤ 4 / 3) := ⟨ido_remaining_chores_cost_le_one_third n m h2n c hc_nonneg h_ido h_mms,
    ido_opposite_pair_cost_le_four_thirds n m h2n c hc_nonneg h_ido h_mms⟩
