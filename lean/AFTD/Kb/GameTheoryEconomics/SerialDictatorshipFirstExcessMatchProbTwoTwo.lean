import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SerialDictatorshipFirstExcessMatchProb

/-!
# serial_dictatorship_first_excess_match_prob_two_two

Topic: matching_markets   Node: cf2a6cee6ea8

Provenance: helper lemma. arXiv:2506.06217, Section 2.1 (Longer Lists Yield Better Matchings)

In a market with 2 unit-capacity schools and list length 2, the match probability p_2(2) of student 3 equals 0.
-/

/-- For 2 schools and list length 2, student 3 matches with probability 0. -/
theorem serial_dictatorship_first_excess_match_prob_two_two : serial_dictatorship_first_excess_match_prob 2 2 = 0 := by
  dsimp [serial_dictatorship_first_excess_match_prob]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  simp only [serial_dictatorship_first_excess_match_prob.dist.eq_2,
    serial_dictatorship_first_excess_match_prob.dist.eq_1]
  norm_num
