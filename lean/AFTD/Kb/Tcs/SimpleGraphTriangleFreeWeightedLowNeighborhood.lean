import AFTD.Prelude

/-!
# simple_graph_triangle_free_weighted_low_neighborhood

Topic: combinatorics   Node: 52383c86154c

Provenance: helper lemma. Weighted-neighborhood argument used in the Ramsey upper-bound proof, https://arxiv.org/abs/2401.00392, Proposition 2.1.

In any finite triangle-free graph with nonnegative integer vertex weights, if some vertex has positive weight then some positive-weight vertex has at most half of the total weight in its neighborhood.
-/

theorem simple_graph_triangle_free_weighted_low_neighborhood {α : Type*} [Fintype α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (w : α → ℕ)
    (htri : G.CliqueFree 3) (hw : ∃ x, 0 < w x) :
    ∃ x, 0 < w x ∧ 2 * (∑ y ∈ G.neighborFinset x, w y) ≤ ∑ y, w y := by
  classical
  by_contra! h
  obtain ⟨x, hx⟩ := hw
  have hlarge : (∑ y, w y) < 2 * (∑ y ∈ G.neighborFinset x, w y) := h x hx
  have hpos : 0 < ∑ y ∈ G.neighborFinset x, w y := by omega
  obtain ⟨y, hy, hwy⟩ := Finset.sum_pos_iff.mp hpos
  have hxy : G.Adj x y := (G.mem_neighborFinset x y).mp hy
  have hdis : Disjoint (G.neighborFinset x) (G.neighborFinset y) := by
    apply Finset.disjoint_left.mpr
    intro z hzx hzy
    have hxz : G.Adj x z := (G.mem_neighborFinset x z).mp hzx
    have hyz : G.Adj y z := (G.mem_neighborFinset y z).mp hzy
    exact (G.isIndepSet_neighborSet_of_triangleFree htri x) hxy hxz (G.ne_of_adj hyz) hyz
  have hbound : (∑ z ∈ G.neighborFinset x, w z) +
      (∑ z ∈ G.neighborFinset y, w z) ≤ ∑ z, w z := by
    rw [← Finset.sum_union hdis]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hylarge : (∑ z, w z) < 2 * (∑ z ∈ G.neighborFinset y, w z) := h y hwy
  omega
