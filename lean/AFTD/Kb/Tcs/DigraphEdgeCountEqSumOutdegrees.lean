import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphEdgeCount

/-!
# digraph_edge_count_eq_sum_outdegrees

Topic: graphs   Node: a4036f950daf

Provenance: helper lemma. Helper for digraph_both_cuts_ge_ceil_div_six_of_indegree_lt, arXiv:2610.21381, proof of Theorem 1.4, Case 2. The two-partition certificate and paired-outcome inequality are a deterministic formulation of the paper's averaging argument; no research advance is claimed.

The number of arcs of a finite digraph equals the sum of its outdegrees.
-/

theorem digraph_edge_count_eq_sum_outdegrees {V : Type*} [Fintype V]
    [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj] :
    digraph_edge_count G = ∑ v, (Finset.univ.filter (G.Adj v)).card := by
  unfold digraph_edge_count
  rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
  simp only [Finset.card_filter]
