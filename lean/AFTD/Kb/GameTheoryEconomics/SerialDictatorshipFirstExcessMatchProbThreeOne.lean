import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SerialDictatorshipFirstExcessMatchProb

/-!
# serial_dictatorship_first_excess_match_prob_three_one

Topic: matching_markets   Node: 869de84e4233

Provenance: helper lemma. arXiv:2506.06217, Section 2.1 (Longer Lists Yield Better Matchings)

In a market with 3 unit-capacity schools and list length 1, the match probability p_3(1) of student 4 equals 8/27.
-/

/-- For 3 schools and list length 1, student 4 matches with probability 8/27. -/
theorem serial_dictatorship_first_excess_match_prob_three_one : serial_dictatorship_first_excess_match_prob 3 1 = 8 / 27 := by
  dsimp [serial_dictatorship_first_excess_match_prob]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  simp only [serial_dictatorship_first_excess_match_prob.dist.eq_2,
             serial_dictatorship_first_excess_match_prob.dist.eq_1]
  norm_num
