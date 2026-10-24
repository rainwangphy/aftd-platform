import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphEdgeCount
import AFTD.Kb.Tcs.DigraphEdgeCountEqSumOutdegrees

/-!
# digraph_edge_count_eq_sum_indegrees

Topic: graphs   Node: f43c4e781f3d

Provenance: helper lemma. Helper for digraph_both_cuts_ge_ceil_div_six_of_indegree_lt, arXiv:2610.21381, proof of Theorem 1.4, Case 2. The two-partition certificate and paired-outcome inequality are a deterministic formulation of the paper's averaging argument; no research advance is claimed.

The number of arcs of a finite digraph equals the sum of its indegrees.
-/

theorem digraph_edge_count_eq_sum_indegrees {V : Type*} [Fintype V]
    [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj] :
    digraph_edge_count G = ∑ v, (Finset.univ.filter fun u => G.Adj u v).card := by
  rw [digraph_edge_count_eq_sum_outdegrees]
  simp only [Finset.card_filter]
  exact Finset.sum_comm
