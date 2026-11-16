import AFTD.Prelude
import AFTD.Kb.Tcs.Op1239Candidate36Tree
import AFTD.Kb.Tcs.Op1239Candidate36MaxDegree
import AFTD.Kb.Tcs.Op1239Candidate36NotLogConcave
import AFTD.Kb.Tcs.PetrialLogConcave
import AFTD.Kb.Tcs.Op1239Candidate36

/-!
# op_1239_subcubic_tree_counterexample

Topic: combinatorics   Node: 7d92e99d0fa5

Provenance: original. Related work: Candidate for OP-1239; computations 28328 and 28332 checks the standard leaf-deletion recurrence from arXiv:2611.07503, Lemma 1.

There exists a tree on Fin 36 with maximum degree at most three whose partial Petrial polynomial is not log-concave.
-/

theorem op_1239_subcubic_tree_counterexample : ∃ G : SimpleGraph (Fin 36), letI : DecidableRel G.Adj := Classical.decRel _; G.IsTree ∧ G.maxDegree ≤ 3 ∧ ¬ petrial_log_concave G := by
  exact ⟨op_1239_candidate36, op_1239_candidate36_tree, op_1239_candidate36_max_degree,
    op_1239_candidate36_not_log_concave⟩
