import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphEdgeCount
import AFTD.Kb.Tcs.DigraphOutdegreeThreeMulLeEdgeCount

/-!
# digraph_abs_net_degree_le_third_of_indegree_lt

Topic: graphs   Node: 91500dbf233c

Provenance: helper lemma. Helper for digraph_both_cuts_ge_ceil_div_six_of_indegree_lt, arXiv:2610.21381, proof of Theorem 1.4, Case 2. The two-partition certificate and paired-outcome inequality are a deterministic formulation of the paper's averaging argument; no research advance is claimed.

Under the low-indegree hypotheses of the target, every absolute net degree is at most one third of the total arc count.
-/

theorem digraph_abs_net_degree_le_third_of_indegree_lt {V : Type*} [Fintype V]
    [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hloop : ∀ v, ¬ G.Adj v v)
    (hdeg : ∀ v, 2 ≤ (Finset.univ.filter (G.Adj v)).card)
    (hin : ∀ v, ((Finset.univ.filter fun u => G.Adj u v).card : ℚ) <
      (digraph_edge_count G : ℚ) / 3 + 1) (v : V) :
    |((Finset.univ.filter (G.Adj v)).card : ℚ) -
      ((Finset.univ.filter fun u => G.Adj u v).card : ℚ)| ≤
        (digraph_edge_count G : ℚ) / 3 := by
  have ho := digraph_outdegree_three_mul_le_edge_count G hloop hdeg v
  have ho' : 3 * ((Finset.univ.filter (G.Adj v)).card : ℚ) ≤
      (digraph_edge_count G : ℚ) := by exact_mod_cast ho
  have hi := hin v
  have hd : (2 : ℚ) ≤ (Finset.univ.filter (G.Adj v)).card := by exact_mod_cast hdeg v
  have hn : (0 : ℚ) ≤ (Finset.univ.filter fun u => G.Adj u v).card := by positivity
  rw [abs_le]
  constructor <;> linarith
