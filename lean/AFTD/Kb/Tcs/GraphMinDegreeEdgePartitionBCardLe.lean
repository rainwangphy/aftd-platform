import AFTD.Prelude
import AFTD.Kb.Tcs.GraphEdgePartitionCard

/-!
# graph_min_degree_edge_partition_b_card_le

Topic: graphs   Node: 29461b54c892

Provenance: helper lemma. step towards exists_idle_measure_wasserstein_dist_lt_one_of_ediam_le_two_and_minDegree_ge

If the minimum degree is at least 2n/3 − 1 and the edge partition has deg x = a + c + 1, deg y = b + c + 1, n = 2 + a + b + c + p, then b ≤ c + 2.
-/

/-- The minimum-degree hypothesis forces at most two more y-private than common neighbours. -/
theorem graph_min_degree_edge_partition_b_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hδ : (2 * (Fintype.card V : ℝ)) / 3 - 1 ≤ (G.minDegree : ℝ))
    (x y : V) (A B C P : Finset V)
    (hdx : G.degree x = A.card + C.card + 1)
    (hdy : G.degree y = B.card + C.card + 1)
    (hn : Fintype.card V = 2 + A.card + B.card + C.card + P.card) :
    B.card ≤ C.card + 2 := by
  have hminx : (G.minDegree : ℝ) ≤ (G.degree x : ℝ) := by
    exact_mod_cast SimpleGraph.minDegree_le_degree G x
  have hminy : (G.minDegree : ℝ) ≤ (G.degree y : ℝ) := by
    exact_mod_cast SimpleGraph.minDegree_le_degree G y
  have hdxR : (G.degree x : ℝ) = (A.card : ℝ) + (C.card : ℝ) + 1 := by
    exact_mod_cast hdx
  have hdyR : (G.degree y : ℝ) = (B.card : ℝ) + (C.card : ℝ) + 1 := by
    exact_mod_cast hdy
  have hnR : (Fintype.card V : ℝ) =
      2 + (A.card : ℝ) + (B.card : ℝ) + (C.card : ℝ) + (P.card : ℝ) := by
    exact_mod_cast hn
  have hx : 2 * (B.card : ℝ) + 2 * (P.card : ℝ) ≤
      (A.card : ℝ) + (C.card : ℝ) + 2 := by
    nlinarith
  have hy : 2 * (A.card : ℝ) + 2 * (P.card : ℝ) ≤
      (B.card : ℝ) + (C.card : ℝ) + 2 := by
    nlinarith
  have hb : (B.card : ℝ) ≤ (C.card : ℝ) + 2 := by
    nlinarith
  exact_mod_cast hb
