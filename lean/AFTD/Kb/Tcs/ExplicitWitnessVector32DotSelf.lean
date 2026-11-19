import AFTD.Prelude
import AFTD.Kb.Tcs.ExplicitWitnessVector32
import AFTD.Kb.Tcs.TwoPowEqSuccIff

/-!
# explicit_witness_vector_32_dot_self

Topic: combinatorics   Node: 873948377ba8

Provenance: helper lemma. arXiv:2611.23269, Eq. (5)

The dot product of explicit_witness_vector_32 with itself equals 10043.
-/

/-- The squared Euclidean norm of the length-32 witness vector is 10043. -/
theorem explicit_witness_vector_32_dot_self :
    dotProduct explicit_witness_vector_32 explicit_witness_vector_32 = 10043 := by first | exact two_pow_eq_succ_iff | (apply two_pow_eq_succ_iff <;> assumption) | (apply two_pow_eq_succ_iff <;> simp_all) | simpa using two_pow_eq_succ_iff | (simp only [explicit_witness_vector_32] at *; first | exact two_pow_eq_succ_iff | (apply two_pow_eq_succ_iff <;> assumption) | (apply two_pow_eq_succ_iff <;> simp_all) | simpa using two_pow_eq_succ_iff)
