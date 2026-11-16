import AFTD.Prelude
import AFTD.Kb.Tcs.Op1239Candidate31
import AFTD.Kb.Tcs.SimpleGraphOfEdgeListDecidableRel
import AFTD.Kb.Tcs.Op1239Candidate31Tree

/-!
# op_1239_candidate31_max_degree

Topic: combinatorics   Node: 67e63e06c213

Provenance: helper lemma. OP-1239, arXiv:2611.07503, Problem 16; candidate from experiments 28663 and 28669.

The maximum degree of op_1239_candidate31 is at most three.
-/

theorem op_1239_candidate31_max_degree : letI : DecidableRel op_1239_candidate31.Adj := Classical.decRel _; op_1239_candidate31.maxDegree ≤ 3 := by
  have h : Classical.decRel op_1239_candidate31.Adj = (Op1239Graph31.adjacency : DecidableRel op_1239_candidate31.Adj) := Subsingleton.elim _ _
  rw [h]
  exact Op1239Graph31.graph_degree
