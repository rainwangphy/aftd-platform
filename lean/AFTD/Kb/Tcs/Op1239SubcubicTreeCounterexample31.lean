import AFTD.Prelude
import AFTD.Kb.Tcs.Op1239Candidate31Tree
import AFTD.Kb.Tcs.Op1239Candidate31MaxDegree
import AFTD.Kb.Tcs.Op1239Candidate31NotLogConcave
import AFTD.Kb.Tcs.PetrialLogConcave
import AFTD.Kb.Tcs.Op1239Candidate31

/-!
# op_1239_subcubic_tree_counterexample31

Topic: combinatorics   Node: 6424714f2425

Provenance: original. Related work: OP-1239, arXiv:2611.07503, Problem 16; candidate from experiments 28663 and 28669.

There exists a tree on Fin 31 with maximum degree at most three whose partial Petrial polynomial is not log-concave.
-/

theorem op_1239_subcubic_tree_counterexample31 : ∃ G : SimpleGraph (Fin 31), letI : DecidableRel G.Adj := Classical.decRel _; G.IsTree ∧ G.maxDegree ≤ 3 ∧ ¬ petrial_log_concave G := ⟨op_1239_candidate31, op_1239_candidate31_tree, op_1239_candidate31_max_degree, op_1239_candidate31_not_log_concave⟩
