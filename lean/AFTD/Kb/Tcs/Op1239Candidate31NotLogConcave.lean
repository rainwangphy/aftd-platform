import AFTD.Prelude
import AFTD.Kb.Tcs.Op1239Candidate31PetrialCoefficients
import AFTD.Kb.Tcs.PetrialLogConcave
import AFTD.Kb.Tcs.Op1239Candidate31
import AFTD.Kb.Tcs.PetrialCoeff

/-!
# op_1239_candidate31_not_log_concave

Topic: combinatorics   Node: 90e75e470338

Provenance: helper lemma. OP-1239, arXiv:2611.07503, Problem 16; candidate from experiments 28663 and 28669.

The partial Petrial polynomial of op_1239_candidate31 is not log-concave.
-/

theorem op_1239_candidate31_not_log_concave : letI : DecidableRel op_1239_candidate31.Adj := Classical.decRel _; ¬ petrial_log_concave op_1239_candidate31 := by
  intro h
  obtain ⟨h1, h2, h3⟩ := op_1239_candidate31_petrial_coefficients
  have h' := h 25 (by refine ⟨24, by omega, ?_⟩; rw [h1]; norm_num)
    (by refine ⟨26, by omega, ?_⟩; rw [h3]; norm_num)
  rw [show 25 - 1 = 24 by decide, show 25 + 1 = 26 by decide, h1, h2, h3] at h'
  norm_num at h'
