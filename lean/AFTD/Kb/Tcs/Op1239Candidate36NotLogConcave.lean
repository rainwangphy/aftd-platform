import AFTD.Prelude
import AFTD.Kb.Tcs.Op1239Candidate36PetrialCoefficients
import AFTD.Kb.Tcs.Op1239CoefficientsForceNotLogConcave
import AFTD.Kb.Tcs.PetrialCoeff
import AFTD.Kb.Tcs.PetrialLogConcave
import AFTD.Kb.Tcs.Op1239Candidate36

/-!
# op_1239_candidate36_not_log_concave

Topic: combinatorics   Node: 4a1d349e66a1

Provenance: helper lemma. Candidate for OP-1239; computations 28328 and 28332 checks the standard leaf-deletion recurrence from arXiv:2611.07503, Lemma 1.

The partial Petrial polynomial of op_1239_candidate36 is not log-concave.
-/

theorem op_1239_candidate36_not_log_concave : letI : DecidableRel op_1239_candidate36.Adj := Classical.decRel _; ¬ petrial_log_concave op_1239_candidate36 := by
  letI : DecidableRel op_1239_candidate36.Adj := Classical.decRel _
  obtain ⟨h1, h2, h3⟩ := op_1239_candidate36_petrial_coefficients
  exact op_1239_coefficients_force_not_log_concave op_1239_candidate36 h1 h2 h3
