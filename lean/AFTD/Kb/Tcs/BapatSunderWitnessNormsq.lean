import AFTD.Prelude
import AFTD.Kb.Tcs.BapatSunderWitnessVector
import AFTD.Kb.Tcs.ExplicitWitnessVector32DotSelf

/-!
# bapat_sunder_witness_normsq

Topic: combinatorics   Node: d301d0840028

Provenance: helper lemma. step towards op_1992_real_bapat_sunder_counterexample_rank_two_or_three

The dot product of the witness vector with itself is 3591.
-/

/-- The witness vector has squared norm 3591. -/
theorem bapat_sunder_witness_normsq :
    dotProduct bapat_sunder_witness_vector bapat_sunder_witness_vector = 3591 := by first | exact explicit_witness_vector_32_dot_self | (apply explicit_witness_vector_32_dot_self <;> assumption) | (apply explicit_witness_vector_32_dot_self <;> simp_all) | simpa using explicit_witness_vector_32_dot_self | (simp only [bapat_sunder_witness_vector] at *; first | exact explicit_witness_vector_32_dot_self | (apply explicit_witness_vector_32_dot_self <;> assumption) | (apply explicit_witness_vector_32_dot_self <;> simp_all) | simpa using explicit_witness_vector_32_dot_self)
