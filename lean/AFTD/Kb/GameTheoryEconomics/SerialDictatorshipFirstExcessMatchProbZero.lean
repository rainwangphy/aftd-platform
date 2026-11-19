import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SerialDictatorshipFirstExcessMatchProb
import AFTD.Kb.GameTheoryEconomics.SerialDictatorshipFirstExcessMatchProbTwoTwo

/-!
# serial_dictatorship_first_excess_match_prob_zero

Topic: matching_markets   Node: 940a63f8fd2a

Provenance: helper lemma. step towards serial_dictatorship_first_excess_optimal_list_sqrt_scale

With an empty preference list a student lists no school at all, hence is never matched: p_n(0) = 0 for every n.
-/

/-- Sanity value at list length 0. -/
theorem serial_dictatorship_first_excess_match_prob_zero (n : ℕ) :
    serial_dictatorship_first_excess_match_prob n 0 = 0 := by first | exact serial_dictatorship_first_excess_match_prob_two_two | (apply serial_dictatorship_first_excess_match_prob_two_two <;> assumption) | (apply serial_dictatorship_first_excess_match_prob_two_two <;> simp_all) | simpa using serial_dictatorship_first_excess_match_prob_two_two | (simp only [serial_dictatorship_first_excess_match_prob] at *; first | exact serial_dictatorship_first_excess_match_prob_two_two | (apply serial_dictatorship_first_excess_match_prob_two_two <;> assumption) | (apply serial_dictatorship_first_excess_match_prob_two_two <;> simp_all) | simpa using serial_dictatorship_first_excess_match_prob_two_two)
