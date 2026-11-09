import AFTD.Prelude
import AFTD.Kb.Tcs.BallotWeight
import AFTD.Kb.Tcs.TwoPowEqSuccIff

/-!
# ballot_weight_zero

Topic: combinatorics   Node: 263f2697dba9

Provenance: helper lemma. arXiv:2611.06860 "Largest Sperner families with bounded VC-dimension", Section 2, above Lemma 2.5

For any natural number $p$, the value of ballot_weight $p$ at 0 equals 1.
-/

/-- The ballot weight at index 0 equals 1. -/
theorem ballot_weight_zero (p : ℕ) : ballot_weight p 0 = 1 := by first | exact two_pow_eq_succ_iff | (apply two_pow_eq_succ_iff <;> assumption) | (apply two_pow_eq_succ_iff <;> simp_all) | simpa using two_pow_eq_succ_iff | (simp only [ballot_weight] at *; first | exact two_pow_eq_succ_iff | (apply two_pow_eq_succ_iff <;> assumption) | (apply two_pow_eq_succ_iff <;> simp_all) | simpa using two_pow_eq_succ_iff)
