import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetThreeWinnerProbEqBothProb
import AFTD.Kb.GameTheoryEconomics.ImpartialCultureWinnerProb
import AFTD.Kb.GameTheoryEconomics.ImpartialCultureWinnerLoserProb

/-!
# condorcet_extremes_three_limit_ratio

Topic: social_choice   Node: a88767eed7e5

Provenance: helper lemma. Guilbaud 1952

If p 3 and q 3 are limits along odd voters 2*k + 1 of the 3-candidate impartial culture probabilities of having a Condorcet winner and having both a winner and loser respectively, and the odd-voter probabilities are equal for all k, and p 3 ≠ 0, then q 3 / (p 3 ^ 2) = 1 / p 3.
-/

/-- For 3 candidates, the ratio of joint to marginal probability is 1 / p_3. -/
theorem condorcet_extremes_three_limit_ratio
    (p q : ℕ → ℝ)
    (h_winner : Filter.Tendsto (fun k => impartial_culture_winner_prob (2 * k + 1) 3) Filter.atTop (nhds (p 3)))
    (h_both : Filter.Tendsto (fun k => impartial_culture_winner_loser_prob (2 * k + 1) 3) Filter.atTop (nhds (q 3)))
    (h_odd : ∀ k, impartial_culture_winner_prob (2 * k + 1) 3 = impartial_culture_winner_loser_prob (2 * k + 1) 3)
    (hp : p 3 ≠ 0) :
    q 3 / (p 3 ^ 2) = 1 / p 3 := by
  have h_same : q 3 = p 3 := by
    have h1 : Filter.Tendsto (fun k => impartial_culture_winner_prob (2 * k + 1) 3) Filter.atTop (nhds (q 3)) := by
      refine Filter.Tendsto.congr ?_ h_both
      intro k
      exact (h_odd k).symm
    exact tendsto_nhds_unique h1 h_winner
  rw [h_same]
  field_simp
