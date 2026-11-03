import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleFreeWeightedLowNeighborhood

/-!
# simple_graph_ramsey_three_ten_nonregular_edge_bound_conditional

Topic: combinatorics   Node: a493cb0ea33b

Provenance: helper lemma. Weighted-neighborhood and edge accounting reduction for OP-926, https://arxiv.org/abs/2401.00392, Proposition 2.1.

Let G be a triangle-free graph on 40 vertices of maximum degree at most 9. Suppose that, for every vertex v, the number of edges outside its closed neighborhood plus the sum of degrees of its neighbors equals the total number of edges. Then either G is 9-regular, or some vertex v has degree less than 9 and its closed non-neighborhood has at most 180 minus 9 times the degree of v edges.
-/

theorem simple_graph_ramsey_three_ten_nonregular_edge_bound_conditional (G : SimpleGraph (Fin 40)) [DecidableRel G.Adj]
    (htri : G.CliqueFree 3) (hmax : ∀ v, G.degree v ≤ 9)
    (hedge : ∀ v : Fin 40,
      (G.induce {u | u ≠ v ∧ ¬ G.Adj v u}).edgeFinset.card +
        (∑ u ∈ G.neighborFinset v, G.degree u) = G.edgeFinset.card) :
    (∀ v, G.degree v = 9) ∨
      ∃ v, G.degree v < 9 ∧
        2 * (G.induce {u | u ≠ v ∧ ¬ G.Adj v u}).edgeFinset.card +
          18 * G.degree v ≤ 360 := by
  classical
  by_cases hn : ∃ v, G.degree v < 9
  · right
    have hw : ∃ x, 0 < 9 - G.degree x := by
      obtain ⟨x, hx⟩ := hn
      exact ⟨x, by omega⟩
    obtain ⟨v, hv, hweight⟩ := simple_graph_triangle_free_weighted_low_neighborhood G (fun y => 9 - G.degree y) htri hw
    refine ⟨v, by omega, ?_⟩
    have hparts (s : Finset (Fin 40)) :
        (∑ x ∈ s, G.degree x) + (∑ x ∈ s, (9 - G.degree x)) = 9 * s.card := by
      rw [← Finset.sum_add_distrib]
      calc
        (∑ x ∈ s, (G.degree x + (9 - G.degree x))) = ∑ _x ∈ s, 9 := by
          apply Finset.sum_congr rfl
          intro x hx
          have h := hmax x
          omega
        _ = 9 * s.card := by simp [mul_comm]
    have hall := hparts Finset.univ
    have hnei := hparts (G.neighborFinset v)
    have hcard : (G.neighborFinset v).card = G.degree v := rfl
    have hhand := G.sum_degrees_eq_twice_card_edges
    have hed := hedge v
    simp only [Finset.card_univ, Fintype.card_fin] at hall
    rw [hcard] at hnei
    omega
  · left
    intro v
    have hv := hmax v
    simp only [not_exists, not_lt] at hn
    have hv' := hn v
    omega
