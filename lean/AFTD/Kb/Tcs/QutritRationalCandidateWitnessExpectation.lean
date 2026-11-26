import AFTD.Prelude
import AFTD.Kb.Tcs.QutritRationalCandidateWitness
import AFTD.Kb.Tcs.QutritConvolutionChoi
import AFTD.Kb.Tcs.QutritRationalCandidateSigma

/-!
# qutrit_rational_candidate_witness_expectation

Topic: quantum   Node: 46e1324e7443

Provenance: helper lemma. OP-2299; candidate witness from computations 39270, 40213 and 40215.

The candidate witness has exactly negative expectation on the candidate Choi matrix.
-/

theorem qutrit_rational_candidate_witness_expectation :
    (∑ p : Fin 3 × Fin 3, ∑ q : Fin 3 × Fin 3,
      qutrit_rational_candidate_witness p q * (qutrit_convolution_choi qutrit_rational_candidate_sigma) q p).re =
      -(5405001211 : ℝ) / 200000000000000 := by
  set_option maxHeartbeats 4000000 in
    simp [qutrit_rational_candidate_witness, qutrit_rational_candidate_witness_flat,
      qutrit_rational_candidate_sigma, qutrit_convolution_choi, Fintype.sum_prod_type,
      Fin.sum_univ_succ, Matrix.of_apply, Fin.add_def, Fin.sub_def]
    <;> norm_num
