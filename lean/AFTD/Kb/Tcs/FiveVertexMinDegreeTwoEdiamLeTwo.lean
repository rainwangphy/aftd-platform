import AFTD.Prelude
import AFTD.Kb.Tcs.EdiamLeTwoOfCardSubOneLeTwoMulMinDegree

/-!
# five_vertex_min_degree_two_ediam_le_two

Topic: graphs   Node: c1e46dd2f21b

Provenance: helper lemma. step towards lly_positive_edge_connectivity_threshold_five

Every graph on 5 vertices with minimum degree at least 2 has diameter at most 2, hence is connected.
-/

/-- A 5-vertex graph of minimum degree 2 has ((card V) − 1)/2 = 2 ≤ δ(G), hence eccentricity-diameter at most 2 (and in particular is connected). -/
theorem five_vertex_min_degree_two_ediam_le_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : Fintype.card V = 5)
    (hδ : 2 ≤ G.minDegree) : G.ediam ≤ 2 := by
  apply ediam_le_two_of_card_sub_one_le_two_mul_minDegree
  rw [hcard]
  norm_num
  exact_mod_cast hδ
