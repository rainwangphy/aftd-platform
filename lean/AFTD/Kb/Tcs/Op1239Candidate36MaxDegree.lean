import AFTD.Prelude
import AFTD.Kb.Tcs.Op1239Candidate36
import AFTD.Kb.Tcs.SimpleGraphOfEdgeListDecidableRel

/-!
# op_1239_candidate36_max_degree

Topic: combinatorics   Node: eac2027ff818

Provenance: helper lemma. Candidate for OP-1239; computations 28328 and 28332 checks the standard leaf-deletion recurrence from arXiv:2611.07503, Lemma 1.

The maximum degree of op_1239_candidate36 is at most 3.
-/

namespace Op1239Degree36
instance adjacency : DecidableRel op_1239_candidate36.Adj := by
  unfold op_1239_candidate36
  exact simple_graph_of_edge_list_decidable_rel _

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem graph_degree : op_1239_candidate36.maxDegree ≤ 3 := by
  apply SimpleGraph.maxDegree_le_of_forall_degree_le
  intro v
  fin_cases v <;> decide


end Op1239Degree36

theorem op_1239_candidate36_max_degree : letI : DecidableRel op_1239_candidate36.Adj := Classical.decRel _; op_1239_candidate36.maxDegree ≤ 3 := by
  have h : Classical.decRel op_1239_candidate36.Adj = (Op1239Degree36.adjacency : DecidableRel op_1239_candidate36.Adj) := Subsingleton.elim _ _
  rw [h]
  exact Op1239Degree36.graph_degree
