import AFTD.Prelude
import AFTD.Kb.Tcs.TeamTail

/-!
# fair_lineup_matching_optimality_essential

Topic: algorithms   Node: b3c5d0ed7f59

Provenance: formalization of a published result. Source: arXiv:2605.21234, Team Order

The matching-optimality condition is essential: the length-5 probability vector [5/6, 5/6, 5/6, 0, 0] has sum 5/2, but its Poisson-binomial probability of at least 3 successes is 125/216, which strictly exceeds 9/16.
-/

/-- A length-5 independent Bernoulli vector with mean 5/2 can achieve majority probability 125/216 > 9/16 without matching optimality. -/
theorem fair_lineup_matching_optimality_essential :
    [(5 : ℝ) / 6, 5 / 6, 5 / 6, 0, 0].sum = 5 / 2 ∧
    team_tail [(5 : ℝ) / 6, 5 / 6, 5 / 6, 0, 0] 3 = 125 / 216 ∧
    (9 : ℝ) / 16 < team_tail [(5 : ℝ) / 6, 5 / 6, 5 / 6, 0, 0] 3 := by
  have h : team_tail [(5 : ℝ) / 6, 5 / 6, 5 / 6, 0, 0] 3 = 125 / 216 := by
    dsimp [team_tail]
    ring
  exact ⟨by norm_num, h, by rw [h]; norm_num⟩
