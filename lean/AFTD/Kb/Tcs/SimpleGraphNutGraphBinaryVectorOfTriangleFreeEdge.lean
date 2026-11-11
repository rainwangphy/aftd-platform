import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsNutGraph

/-!
# simple_graph_nut_graph_binary_vector_of_triangle_free_edge

Topic: graphs   Node: 04f35e416f24

Provenance: helper lemma. step towards op_1267_diameter_two_nut_graph_has_binary_vector

If a finite simple nut graph with at least 4 vertices has a triangle-free edge (an edge whose endpoints share no common neighbors), then the sum of the rows of its endpoints is a non-row (0,1)-vector in the row space of the adjacency matrix.
-/

/-- If a finite simple nut graph on at least 4 vertices has a triangle-free edge, then the sum of its endpoint rows is a non-row (0,1)-vector in the row space of the adjacency matrix. -/
theorem simple_graph_nut_graph_binary_vector_of_triangle_free_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnut : simple_graph_is_nut_graph G) (hcard : 4 ≤ Fintype.card V)
    (u v : V) (hadj : G.Adj u v) (htri : ∀ w : V, ¬(G.Adj u w ∧ G.Adj v w)) :
    ∃ y : V → ℝ, (∀ w : V, y w = 0 ∨ y w = 1) ∧ y ≠ 0 ∧
      y ∈ LinearMap.range (Matrix.toLin' (G.adjMatrix ℝ)) ∧
      ∀ l : V, y ≠ G.adjMatrix ℝ l := by
  classical
  refine ⟨fun w => G.adjMatrix ℝ w u + G.adjMatrix ℝ w v, ?_, ?_, ?_, ?_⟩
  · -- y is a (0,1)-vector, since no vertex is adjacent to both u and v
    intro w
    simp only [SimpleGraph.adjMatrix_apply]
    by_cases h1 : G.Adj w u
    · by_cases h2 : G.Adj w v
      · exact absurd ⟨(G.adj_comm w u).1 h1, (G.adj_comm w v).1 h2⟩ (htri w)
      · right; simp [h1, h2]
    · by_cases h2 : G.Adj w v
      · right; simp [h1, h2]
      · left; simp [h1, h2]
  · -- y ≠ 0, since y v = 1
    intro h
    have hv : (fun w => G.adjMatrix ℝ w u + G.adjMatrix ℝ w v) v = 0 := by rw [h]; rfl
    simp only [SimpleGraph.adjMatrix_apply, SimpleGraph.irrefl G, if_false, add_zero,
      if_pos ((G.adj_comm v u).2 hadj)] at hv
    exact one_ne_zero hv
  · -- y is the image of the (0,1)-vector e_u + e_v
    refine LinearMap.mem_range.2 ⟨Pi.single u 1 + Pi.single v 1, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_add, Matrix.mulVec_single_one, Matrix.mulVec_single_one]
    funext w
    simp [Matrix.col_apply]
  · -- y is not a row: otherwise e_u + e_v - e_l would be a sparse null vector
    intro l hy
    have hsym : ∀ a b : V, G.adjMatrix ℝ a b = G.adjMatrix ℝ b a := by
      intro a b; simp [SimpleGraph.adjMatrix_apply, G.adj_comm]
    set z : V → ℝ := Pi.single u 1 + Pi.single v 1 - Pi.single l 1 with hzdef
    have hker : z ∈ (Matrix.toLin' (G.adjMatrix ℝ)).ker := by
      rw [LinearMap.mem_ker, Matrix.toLin'_apply, hzdef, Matrix.mulVec_sub, Matrix.mulVec_add,
        Matrix.mulVec_single_one, Matrix.mulVec_single_one, Matrix.mulVec_single_one]
      funext w
      simp only [Pi.sub_apply, Pi.add_apply, Matrix.col_apply, Pi.zero_apply]
      have hyw : G.adjMatrix ℝ w u + G.adjMatrix ℝ w v = G.adjMatrix ℝ l w := congrFun hy w
      rw [hyw, hsym l w, sub_self]
    have huv : u ≠ v := G.ne_of_adj hadj
    have hzne : z ≠ 0 := by
      intro hz0
      have hzv : z v = 0 := by rw [hz0]; rfl
      have hzu : z u = 0 := by rw [hz0]; rfl
      by_cases hlu : l = u
      · rw [hzdef] at hzv
        simp only [Pi.sub_apply, Pi.add_apply] at hzv
        rw [Pi.single_eq_same, Pi.single_eq_of_ne huv.symm, hlu, Pi.single_eq_of_ne huv.symm] at hzv
        norm_num at hzv
      · rw [hzdef] at hzu
        simp only [Pi.sub_apply, Pi.add_apply] at hzu
        rw [Pi.single_eq_same, Pi.single_eq_of_ne huv, Pi.single_eq_of_ne (Ne.symm hlu)] at hzu
        norm_num at hzu
    have hzero : ∃ w : V, z w = 0 := by
      have hlt : ({u, v, l} : Finset V).card < (Finset.univ : Finset V).card := by
        rw [Finset.card_univ]
        have h1 : ({u, v, l} : Finset V) = insert u (insert v {l}) := rfl
        have a := Finset.card_insert_le u (insert v ({l} : Finset V))
        have b := Finset.card_insert_le v ({l} : Finset V)
        have c : ({l} : Finset V).card = 1 := Finset.card_singleton l
        omega
      obtain ⟨w, -, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      refine ⟨w, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
      obtain ⟨hwu, hwv, hwl⟩ := hw
      rw [hzdef]
      simp only [Pi.sub_apply, Pi.add_apply]
      rw [Pi.single_eq_of_ne hwu, Pi.single_eq_of_ne hwv, Pi.single_eq_of_ne hwl]
      norm_num
    obtain ⟨w, hw⟩ := hzero
    exact hnut.2 z hker hzne w hw
