import AFTD.Prelude
import AFTD.Kb.Tcs.EdiamLeTwoOfCardSubOneLeTwoMulMinDegree

/-!
# ediam_le_two_of_minDegree_ge_two_thirds

Topic: graphs   Node: 83384faf8a69

Provenance: helper lemma. step towards lly_curvature_pos_of_edge_connectivity_ge

If a finite connected graph G on at least two vertices has minimum degree δ(G) ≥ 2n/3 − 1, then its diameter is at most 2.
-/

/-- A connected graph on at least two vertices with minimum degree δ(G) ≥ 2n/3 - 1 has diameter at most 2. -/
theorem ediam_le_two_of_minDegree_ge_two_thirds
    {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hδ : (2 * (Fintype.card V : ℝ)) / 3 - 1 ≤ (G.minDegree : ℝ)) :
    G.ediam ≤ 2 := by
  have hn : 1 < Fintype.card V := Fintype.one_lt_card
  rcases lt_or_ge (Fintype.card V) 3 with hlt | hge
  · have hcard : Fintype.card V = 2 := by omega
    have hmin : (1 : ℝ) ≤ (G.minDegree : ℝ) := by
      exact_mod_cast (hG.preconnected.minDegree_pos_of_nontrivial : 0 < G.minDegree)
    apply ediam_le_two_of_card_sub_one_le_two_mul_minDegree
    rw [hcard]
    norm_num
    linarith
  · apply ediam_le_two_of_card_sub_one_le_two_mul_minDegree
    have hnR : (3 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hge
    nlinarith
