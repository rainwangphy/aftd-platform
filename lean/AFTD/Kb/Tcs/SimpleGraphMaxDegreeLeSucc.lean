import AFTD.Prelude

/-!
# simple_graph_maxDegree_le_succ

Topic: graphs   Node: 14c023b2ac7c

Provenance: helper lemma. folklore

If a finite simple graph G has maximum degree at most k, then its maximum degree is at most k + 1.
-/

/-- A graph with maxDegree ≤ k also satisfies maxDegree ≤ k + 1. -/
theorem simple_graph_maxDegree_le_succ {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (h : G.maxDegree ≤ k) : G.maxDegree ≤ k + 1 := Nat.le_succ_of_le h
