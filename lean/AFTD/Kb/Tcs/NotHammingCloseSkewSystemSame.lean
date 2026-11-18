import AFTD.Prelude
import AFTD.Kb.Tcs.HammingCloseSkewSystem
import AFTD.Kb.Tcs.FinThreeFalseOfFourPairwiseNe

/-!
# not_hamming_close_skew_system_same

Topic: combinatorics   Node: c5b1c2c99e68

Provenance: helper lemma. arXiv:2611.20820 Sec. 5.7

The constant all-false vector paired with itself in {0,1}^2 does not form a close-skew system of radius 1 and size 1.
-/

/-- Sanity lemma: identical vectors do not form a close-skew system because the witness must be at distance at least r + 1. -/
theorem not_hamming_close_skew_system_same :
    ¬ hamming_close_skew_system 1 (fun (_ : Fin 1) (_ : Fin 2) => false) (fun (_ : Fin 1) (_ : Fin 2) => false) := by first | exact fin_three_false_of_four_pairwise_ne | (apply fin_three_false_of_four_pairwise_ne <;> assumption) | (apply fin_three_false_of_four_pairwise_ne <;> simp_all) | simpa using fin_three_false_of_four_pairwise_ne | (simp only [hamming_close_skew_system] at *; first | exact fin_three_false_of_four_pairwise_ne | (apply fin_three_false_of_four_pairwise_ne <;> assumption) | (apply fin_three_false_of_four_pairwise_ne <;> simp_all) | simpa using fin_three_false_of_four_pairwise_ne)
