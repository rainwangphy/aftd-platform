import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialLogConcave
import AFTD.Kb.Tcs.PetrialCoeff

/-!
# op_1239_coefficients_force_not_log_concave

Topic: combinatorics   Node: e5fd90b85947

Provenance: helper lemma. Candidate for OP-1239; computations 28328 and 28332 checks the standard leaf-deletion recurrence from arXiv:2611.07503, Lemma 1.

Any finite simple graph whose partial Petrial coefficients in ranks 27, 28, and 29 are respectively 256, 32640, and 4666944 fails partial Petrial log-concavity.
-/

theorem op_1239_coefficients_force_not_log_concave {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (h1 : petrial_coeff G 27 = 256) (h2 : petrial_coeff G 28 = 32640) (h3 : petrial_coeff G 29 = 4666944) : ¬ petrial_log_concave G := by
  intro h
  have h' := h 28 (by refine ⟨27, by omega, ?_⟩; rw [h1]; norm_num)
    (by refine ⟨29, by omega, ?_⟩; rw [h3]; norm_num)
  rw [show 28-1=27 by decide, show 28+1=29 by decide, h1, h2, h3] at h'
  norm_num at h'
